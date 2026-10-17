import InitECandidate.Runtime.HashNewSafePlanGeometry
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

theorem htabNew_header_separate_of_safe_plan (table keyLength capacity : BitVec 64)
    (pointerBound : table.toNat ≤ 33806089496) (tableAligned : table.toNat % 8 = 0)
    (safe : AllocationPlanSafe table (htabNewAllocationSizes keyLength capacity))
    (offset : Nat) (field : offset ≤ 64) :
    ∀ index : BitVec 64, index.toNat < capacity.toNat →
      panByteAlignHOL (htabNewUsed table keyLength capacity + index) ≠ table + BitVec.ofNat 64 offset := by
  have plan := safe
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
theorem htabNew_header_store_preserves_count_of_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keyLength capacity value : BitVec 64)
    (pointerBound : table.toNat ≤ 33806089496) (tableAligned : table.toNat % 8 = 0)
    (safe : AllocationPlanSafe table (htabNewAllocationSizes keyLength capacity))
    (offset : Nat) (field : offset ≤ 64) :
    hashOccupiedCount capacity (hashOccupancyRead
      (sourceWriteWord state (table + BitVec.ofNat 64 offset) value)
      (htabNewUsed table keyLength capacity)) =
    hashOccupiedCount capacity (hashOccupancyRead state (htabNewUsed table keyLength capacity)) :=
  sourceWriteWord_occupancy_preserved state capacity (htabNewUsed table keyLength capacity)
    (table + BitVec.ofNat 64 offset) value
    (htabNew_header_separate_of_safe_plan table keyLength capacity pointerBound tableAligned safe offset field)

theorem htabNew_keys_before_values_of_safe_plan (table keyLength capacity : BitVec 64)
    (keyBound : keyLength.toNat ≤ 52)
    (safe : AllocationPlanSafe table (htabNewAllocationSizes keyLength capacity)) :
    (allocationEnd table 72).toNat + capacity.toNat * (allocationEnd 0 keyLength).toNat ≤
      (htabNewValues table keyLength capacity).toNat := by
  have capacityBound := htabNew_capacity_bound_of_safe_plan table keyLength capacity safe
  obtain ⟨_,before,guard,_,_⟩ := safe
  have stride := htabNew_stride_bound keyLength keyBound
  have productBound := Nat.mul_le_mul_left capacity.toNat stride.2.1
  have product : (capacity * allocationEnd 0 keyLength).toNat =
      capacity.toNat * (allocationEnd 0 keyLength).toNat :=
    BitVec.toNat_mul_of_lt (by omega)
  have covers := allocationEnd_covers (allocationEnd table 72) (capacity * allocationEnd 0 keyLength)
    (allocationGuard_sum_bound _ _ before guard)
  simpa only [htabNewValues,allocationPlanEnd,product] using covers.1

#print axioms htabNew_header_separate_of_safe_plan
#print axioms htabNew_header_store_preserves_count_of_safe_plan
#print axioms htabNew_keys_before_values_of_safe_plan
end InitECandidate.Runtime
