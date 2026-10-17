import InitECandidate.Runtime.HashGrowZeroHeaderSource
import InitECandidate.Runtime.HashGrowSafePlanLayout
import InitECandidate.Runtime.HashTableArraysInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual original zeroing/header prefix establishes the relocated table
invariant at rehash entry, deriving every load/store domain from the allocation. -/
theorem evaluate_htabGrow_zero_invariant_width_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer capacity stride : BitVec 64) (bits : Nat) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode) (power : capacity.toNat = 2 ^ bits)
    (strideAligned : stride.toNat % 8 = 0) (fits : keyLength.toNat ≤ stride.toNat) (strideBound : stride.toNat ≤ 56)
    (pointerAligned : pointer.toNat % 8 = 0) (headerBefore : table.toNat + 72 ≤ pointer.toNat)
    (pointerBound : pointer.toNat ≤ 33806089496)
    (capacityBound : capacity.toNat ≤ 33806089496)
    (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (ticks : (capacity * 2).toNat + 1 ≤ state.clock)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (keyField : state.memory (table + 0) = .word keyLength)
    (strideField : state.memory (table + 8) = .word stride)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (ncapLocal : state.locals.lookup (ofString "ncap") = some (.val (.word (capacity * 2))))
    (nkeysLocal : state.locals.lookup (ofString "nkeys") = some (.val (.word pointer)))
    (nvalsLocal : state.locals.lookup (ofString "nvals") = some (.val (.word (htabGrowValues pointer capacity stride))))
    (nusedLocal : state.locals.lookup (ofString "nused") = some (.val (.word (htabGrowUsed pointer capacity stride))))
    (norderLocal : state.locals.lookup (ofString "norder") = some (.val (.word (htabGrowOrder pointer capacity stride))))
    (norder_posLocal : state.locals.lookup (ofString "norder_pos") = some (.val (.word (htabGrowOrderPos pointer capacity stride)))) :
    ∃ ready, evaluateHOLFiniteState state (hashGrowZeroHeader continuation) = evaluateHOLFiniteState ready continuation ∧
      HashTableArraysInvariant keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
        (htabGrowOrderPos pointer capacity stride) 0 (bits + 1) ready ∧
      state.clock ≤ ready.clock + (capacity * 2).toNat + 1 ∧ ready.clock ≤ state.clock ∧
      ready.locals = state.locals ∧ ready.globals = state.globals ∧ ready.code = state.code ∧
      ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧
      (∀ watched : BitVec 64, table.toNat + 72 ≤ watched.toNat → watched.toNat < pointer.toNat →
        ready.memory watched = state.memory watched) := by
  obtain ⟨ka,va,ua,oa,ra,hk,hv,ku,vu,uo,orr,limit⟩ :=
    htabGrow_array_layout_from_safe_plan table pointer capacity stride strideBound pointerAligned headerBefore pointerBound capacityBound safePlan
  have headerDomain : ∀ offset : Nat, offset ≤ 64 → state.memaddrs (table + BitVec.ofNat 64 offset) := by
    intro offset small
    have natural : (BitVec.ofNat 64 offset).toNat = offset := by
      change offset % 2 ^ 64 = offset
      exact Nat.mod_eq_of_lt (by omega)
    have address : (table + BitVec.ofNat 64 offset).toNat = table.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    apply domain <;> omega
  have wordDomain : ∀ offset : Nat, offset < (capacity * 2).toNat →
      state.memaddrs (htabGrowUsed pointer capacity stride + BitVec.ofNat 64 offset) := by
    intro offset inside
    have natural : (BitVec.ofNat 64 offset).toNat = offset := by
      change offset % 2 ^ 64 = offset
      exact Nat.mod_eq_of_lt (Nat.lt_trans inside (capacity * 2).isLt)
    have address : (htabGrowUsed pointer capacity stride + BitVec.ofNat 64 offset).toNat =
        (htabGrowUsed pointer capacity stride).toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    apply domain <;> omega
  have byteDomain : ∀ offset : Nat, offset < (capacity * 2).toNat →
      state.memaddrs (panByteAlignHOL (htabGrowUsed pointer capacity stride + BitVec.ofNat 64 offset)) := by
    intro offset inside
    have natural : (BitVec.ofNat 64 offset).toNat = offset := by
      change offset % 2 ^ 64 = offset
      exact Nat.mod_eq_of_lt (Nat.lt_trans inside (capacity * 2).isLt)
    have interval := hashOccupancy_aligned_interval (htabGrowUsed pointer capacity stride) (capacity * 2)
      (BitVec.ofNat 64 offset) ua (by omega) (by rw [natural]; exact inside)
    apply domain <;> omega
  obtain ⟨ready,run,empty,cost,remaining,locals,globals,postCode,addresses,endian,c0,c8,c16,c24,c32,c40,c48,c56,c64,zeroFrame⟩ :=
    evaluate_htabGrow_zero_header state table (capacity * 2) pointer (htabGrowValues pointer capacity stride)
      (htabGrowUsed pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride)
      continuation code ticks ua (by omega) (by omega) tableLocal ncapLocal nkeysLocal nvalsLocal nusedLocal norderLocal
      norder_posLocal headerDomain wordDomain byteDomain
  have doubled : (capacity * (2 : BitVec 64)).toNat = 2 * capacity.toNat := by
    rw [BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)]
    change capacity.toNat * 2 = 2 * capacity.toNat
    omega
  have nextPower : (capacity * (2 : BitVec 64)).toNat = 2 ^ (bits + 1) := by
    rw [doubled,power,Nat.pow_succ]
    omega
  have preserved : ∀ watched : BitVec 64, table.toNat + 72 ≤ watched.toNat → watched.toNat < pointer.toNat →
      ready.memory watched = state.memory watched := by
    intro watched lower upper
    exact zeroFrame watched lower (by omega)
  refine ⟨ready,run,?_,cost,remaining,locals,globals,postCode,addresses,endian,preserved⟩
  exact {
    code := postCode.trans code
    power := nextPower
    keysAligned := ka
    strideAligned := strideAligned
    valuesAligned := va
    usedAligned := ua
    orderAligned := oa
    orderPosAligned := ra
    headerKeys := hk
    headerValues := hv
    keysBefore := ku
    valuesBefore := vu
    usedBefore := uo
    orderBefore := orr
    endBound := limit
    fits := fits
    domain := by rw [addresses]; exact domain
    cell0 := c0.trans keyField
    cell8 := c8.trans strideField
    cell16 := c16
    cell24 := c24
    cell32 := c32
    cell40 := c40
    cell48 := c48
    cell56 := c56
    cell64 := c64
    agreement := empty.symm
    room := by change 0 < (capacity * 2).toNat; rw [nextPower]; exact Nat.two_pow_pos _
  }

#print axioms evaluate_htabGrow_zero_invariant_width_safe_plan
end InitECandidate.Runtime
