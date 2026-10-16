import InitECandidate.Runtime.AllocationPlanFacts
import InitECandidate.Runtime.HashNewAllocationPlan
import InitECandidate.Runtime.HashOccupancyPreservation
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Occupancy starts after the header, keys and values allocations. -/
def htabNewUsed (table keyLength capacity : BitVec 64) : BitVec 64 :=
  allocationPlanEnd table [72,capacity * allocationEnd 0 keyLength,capacity * 8]

/-- Every header field lies strictly before every aligned occupancy cell.
This discharges separation for the three pointer stores following memzero. -/
theorem htabNew_header_separate (table keyLength capacity : BitVec 64)
    (keyBound : keyLength.toNat ≤ 52) (tableAligned : table.toNat % 8 = 0)
    (budget : table.toNat + 81 * capacity.toNat + 114 ≤ 33806089496)
    (offset : Nat) (field : offset ≤ 64) :
    ∀ index : BitVec 64, index.toNat < capacity.toNat →
      panByteAlignHOL (htabNewUsed table keyLength capacity + index) ≠ table + BitVec.ofNat 64 offset := by
  have plan := (htabNew_allocation_plan_safe table keyLength capacity keyBound budget).1
  obtain ⟨g1,b1,g2,b2,g3,b3,g4,_,_⟩ := plan
  have prefixSafe : AllocationPlanSafe table
      [72,capacity * allocationEnd 0 keyLength,capacity * 8] := ⟨g1,b1,g2,b2,g3,b3,b3⟩
  have facts := allocationPlan_facts _ table prefixSafe (by omega) tableAligned
  have lower := facts.1
  change table.toNat + (72 + ((capacity * allocationEnd 0 keyLength).toNat +
    ((capacity * 8).toNat + 0))) ≤ (htabNewUsed table keyLength capacity).toNat at lower
  have usedBound : (htabNewUsed table keyLength capacity).toNat ≤ 33806089496 := b3
  have usedAligned : (htabNewUsed table keyLength capacity).toNat % 8 = 0 := facts.2.2
  have sumBound := allocationGuard_sum_bound (htabNewUsed table keyLength capacity) capacity usedBound g4
  have offsetSmall : offset < 2 ^ 64 := by omega
  have offsetNat : (BitVec.ofNat 64 offset).toNat = offset := by change offset % 2 ^ 64 = offset; exact Nat.mod_eq_of_lt offsetSmall
  have noWrap : table.toNat + (BitVec.ofNat 64 offset).toNat < 2 ^ 64 := by rw [offsetNat]; omega
  apply hashOccupancy_separate_allocation _ _ _ usedAligned (by omega)
  left
  rw [BitVec.toNat_add_of_lt noWrap,offsetNat]
  omega

/-- Header pointer stores after occupancy initialization preserve its count. -/
theorem htabNew_header_store_preserves_count {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keyLength capacity value : BitVec 64)
    (keyBound : keyLength.toNat ≤ 52) (tableAligned : table.toNat % 8 = 0)
    (budget : table.toNat + 81 * capacity.toNat + 114 ≤ 33806089496)
    (offset : Nat) (field : offset ≤ 64) :
    hashOccupiedCount capacity (hashOccupancyRead
      (sourceWriteWord state (table + BitVec.ofNat 64 offset) value)
      (htabNewUsed table keyLength capacity)) =
    hashOccupiedCount capacity (hashOccupancyRead state (htabNewUsed table keyLength capacity)) :=
  sourceWriteWord_occupancy_preserved state capacity (htabNewUsed table keyLength capacity)
    (table + BitVec.ofNat 64 offset) value
    (htabNew_header_separate table keyLength capacity keyBound tableAligned budget offset field)

#print axioms htabNew_header_store_preserves_count
#print axioms htabNew_header_separate
end InitECandidate.Runtime
