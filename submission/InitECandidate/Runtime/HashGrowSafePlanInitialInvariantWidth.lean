import InitECandidate.Runtime.HashGrowSafePlanLayout
import InitECandidate.Runtime.HashGrowHeaderOccupancy
import InitECandidate.Runtime.HashGrowHeaderState
import InitECandidate.Runtime.HashTableArraysInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- After zeroing new occupancy and executing the original header stores,
growth has an empty generalized table invariant at doubled capacity. -/
theorem htabGrow_initial_invariant_width_from_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer capacity stride : BitVec 64) (bits : Nat)
    (code : state.code = originalRuntimeCode) (power : capacity.toNat = 2 ^ bits)
    (strideAligned : stride.toNat % 8 = 0) (fits : keyLength.toNat ≤ stride.toNat) (strideBound : stride.toNat ≤ 56)
    (pointerAligned : pointer.toNat % 8 = 0) (headerBefore : table.toNat + 72 ≤ pointer.toNat)
    (pointerBound : pointer.toNat ≤ 33806089496)
    (capacityBound : capacity.toNat ≤ 33806089496)
    (safe : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (keyField : state.memory (table + 0) = .word keyLength)
    (strideField : state.memory (table + 8) = .word stride)
    (empty : hashOccupiedCount (capacity * 2) (hashOccupancyRead state (htabGrowUsed pointer capacity stride)) = 0) :
    HashTableArraysInvariant keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
      (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
      (htabGrowOrderPos pointer capacity stride) 0 (bits + 1)
      (htabGrowHeaderPost state table (capacity * 2) pointer (htabGrowValues pointer capacity stride)
        (htabGrowUsed pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride)) := by
  obtain ⟨ka,va,ua,oa,ra,hk,hv,ku,vu,uo,orr,limit⟩ :=
    htabGrow_array_layout_from_safe_plan table pointer capacity stride strideBound pointerAligned headerBefore pointerBound capacityBound safe
  have doubled : (capacity * (2 : BitVec 64)).toNat = 2 * capacity.toNat := by
    rw [BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)]
    change capacity.toNat * 2 = 2 * capacity.toNat
    omega
  have nextPower : (capacity * (2 : BitVec 64)).toNat = 2 ^ (bits + 1) := by
    rw [doubled,power,Nat.pow_succ]
    omega
  obtain ⟨c16,c32,c40,c48,c56,c64,c24,c0,c8⟩ := htabGrowHeaderPost_fields state table (capacity * 2) pointer
    (htabGrowValues pointer capacity stride) (htabGrowUsed pointer capacity stride)
    (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride)
  have countPreserved := htabGrow_header_preserves_occupancy state table (capacity * 2) pointer
    (htabGrowValues pointer capacity stride) (htabGrowUsed pointer capacity stride)
    (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride) ua (by omega) (by omega)
  rw [htabGrowHeaderPost_state] at countPreserved ⊢
  exact {
    code := code
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
    domain := domain
    cell0 := c0.trans keyField
    cell8 := c8.trans strideField
    cell16 := c16
    cell24 := c24
    cell32 := c32
    cell40 := c40
    cell48 := c48
    cell56 := c56
    cell64 := c64
    agreement := (countPreserved.trans empty).symm
    room := by change 0 < (capacity * 2).toNat; rw [nextPower]; exact Nat.two_pow_pos _
  }

#print axioms htabGrow_initial_invariant_width_from_safe_plan
end InitECandidate.Runtime
