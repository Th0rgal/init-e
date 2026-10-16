import InitECandidate.Runtime.HashGrowLayout
import InitECandidate.Runtime.HashGrowHeaderOccupancy
import InitECandidate.Runtime.HashTableArraysInvariant32
set_option maxHeartbeats 2000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- After zeroing new occupancy and executing the original header stores,
growth has an empty generalized table invariant at doubled capacity. -/
theorem htabGrow_initial_invariant32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer capacity stride : BitVec 64) (bits : Nat)
    (code : state.code = originalRuntimeCode) (power : capacity.toNat = 2 ^ bits)
    (strideAligned : stride.toNat % 8 = 0) (fits : 32 ≤ stride.toNat) (strideBound : stride.toNat ≤ 56)
    (pointerAligned : pointer.toNat % 8 = 0) (headerBefore : table.toNat + 72 ≤ pointer.toNat)
    (budget : pointer.toNat + 162 * capacity.toNat + 35 ≤ 33806089496)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (keyField : state.memory (table + 0) = .word (32 : BitVec 64))
    (strideField : state.memory (table + 8) = .word stride)
    (empty : hashOccupiedCount (capacity * 2) (hashOccupancyRead state (htabGrowUsed pointer capacity stride)) = 0) :
    HashTableArraysInvariant32 table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
      (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
      (htabGrowOrderPos pointer capacity stride) 0 (bits + 1)
      (htabGrowHeaderPost state table (capacity * 2) pointer (htabGrowValues pointer capacity stride)
        (htabGrowUsed pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride)) := by
  obtain ⟨ka,va,ua,oa,ra,hk,hv,ku,vu,uo,orr,limit⟩ :=
    htabGrow_array_layout table pointer capacity stride strideBound pointerAligned headerBefore budget
  have doubled := (htabGrow_allocation_plan_safe pointer capacity stride strideBound budget).1
  have nextPower : (capacity * (2 : BitVec 64)).toNat = 2 ^ (bits + 1) := by
    rw [doubled,power,Nat.pow_succ]
    omega
  obtain ⟨c16,c32,c40,c48,c56,c64,c24,c0,c8⟩ := htabGrowHeaderPost_fields state table (capacity * 2) pointer
    (htabGrowValues pointer capacity stride) (htabGrowUsed pointer capacity stride)
    (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride)
  have countPreserved := htabGrow_header_preserves_occupancy state table (capacity * 2) pointer
    (htabGrowValues pointer capacity stride) (htabGrowUsed pointer capacity stride)
    (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride) ua (by omega) (by omega)
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

#print axioms htabGrow_initial_invariant32
end InitECandidate.Runtime
