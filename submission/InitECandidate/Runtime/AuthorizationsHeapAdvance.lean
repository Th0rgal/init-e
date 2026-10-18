import InitECandidate.Runtime.AllocationAligned
namespace InitECandidate.Runtime
open Flapjack

/-- The six-field inner array occupies exactly 96 bytes at an aligned frontier. -/
theorem authorization_heap_advance (pointer : BitVec 64)
    (bounded : pointer.toNat + 96 ≤ 33806089496)
    (aligned : pointer.toNat % 8 = 0) :
    (allocationEnd pointer 96).toNat = pointer.toNat + 96 := by
  exact allocationEnd_aligned_toNat pointer 96 bounded aligned (by decide)

/-- A reserve for remaining iterations survives the next fixed-size allocation. -/
theorem authorization_heap_reserve (pointer : BitVec 64) (remaining reserve ceiling : Nat)
    (aligned : pointer.toNat % 8 = 0)
    (within : pointer.toNat + 96 ≤ 33806089496)
    (budget : pointer.toNat + 96 * (remaining + 1) + reserve ≤ ceiling) :
    pointer.toNat ≤ (allocationEnd pointer 96).toNat ∧
      (allocationEnd pointer 96).toNat + 96 * remaining + reserve ≤ ceiling := by
  rw [authorization_heap_advance pointer within aligned]
  omega

#print axioms authorization_heap_advance
#print axioms authorization_heap_reserve
end InitECandidate.Runtime
