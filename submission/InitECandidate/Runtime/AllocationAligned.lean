import InitECandidate.Runtime.AllocationRound
namespace InitECandidate.Runtime
open Flapjack

/-- Natural heap bounds imply the unsigned request guard used by alloc. -/
theorem allocationGuard_of_sum_bound (pointer size : BitVec 64)
    (bounded : pointer.toNat + size.toNat ≤ 33806089496) :
    size ≤ (33806089496 : BitVec 64) - pointer := by
  have pointerBound : pointer ≤ (33806089496 : BitVec 64) := BitVec.le_def.mpr (by change pointer.toNat ≤ 33806089496; omega)
  apply BitVec.le_def.mpr
  rw [BitVec.toNat_sub_of_le pointerBound]
  change size.toNat ≤ 33806089496 - pointer.toNat
  omega

/-- Aligned allocations whose size is a multiple of eight need no padding. -/
theorem allocationEnd_aligned_toNat (pointer size : BitVec 64)
    (bounded : pointer.toNat + size.toNat ≤ 33806089496)
    (pointerAligned : pointer.toNat % 8 = 0) (sizeAligned : size.toNat % 8 = 0) :
    (allocationEnd pointer size).toNat = pointer.toNat + size.toNat := by
  have rounded := allocationEnd_covers pointer size bounded
  have p := Nat.mod_add_div pointer.toNat 8
  have s := Nat.mod_add_div size.toNat 8
  have e := Nat.mod_add_div (allocationEnd pointer size).toNat 8
  omega

/-- A heap-bounded array product is represented exactly by source word
multiplication. This also supplies the allocator's unsigned request guard. -/
theorem allocation_product_request (pointer count width : BitVec 64)
    (bounded : pointer.toNat + count.toNat * width.toNat ≤ 33806089496) :
    (count * width).toNat = count.toNat * width.toNat ∧
      count * width ≤ (33806089496 : BitVec 64) - pointer := by
  have product : count.toNat * width.toNat < 2 ^ 64 := by omega
  have exactProduct := BitVec.toNat_mul_of_lt product
  refine ⟨exactProduct,allocationGuard_of_sum_bound pointer (count * width) ?_⟩
  rw [exactProduct]
  exact bounded

/-- Reserving seven padding bytes discharges both allocator guards and
provides alignment and disjointness for the following allocation. -/
theorem allocation_success_bounds (pointer size : BitVec 64)
    (bounded : pointer.toNat + size.toNat + 7 ≤ 33806089496) :
    size ≤ (33806089496 : BitVec 64) - pointer ∧
      (allocationEnd pointer size).toNat ≤ 33806089496 ∧
      pointer.toNat + size.toNat ≤ (allocationEnd pointer size).toNat ∧
      (allocationEnd pointer size).toNat % 8 = 0 := by
  have sumBound : pointer.toNat + size.toNat ≤ 33806089496 := by omega
  have covered := allocationEnd_covers pointer size sumBound
  exact ⟨allocationGuard_of_sum_bound pointer size sumBound,by omega,covered.1,covered.2.2⟩

#print axioms allocation_success_bounds
#print axioms allocationGuard_of_sum_bound
#print axioms allocationEnd_aligned_toNat
#print axioms allocation_product_request
end InitECandidate.Runtime
