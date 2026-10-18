import InitECandidate.Runtime.AllocationAligned
namespace InitECandidate.Runtime
open Flapjack

/-- Aligned key-buffer allocation consumes precisely 32 bytes per key. -/
theorem access_keys_heap_advance (pointer count : BitVec 64)
    (aligned : pointer.toNat % 8 = 0)
    (bounded : pointer.toNat + count.toNat * 32 ≤ 33806089496) :
    (allocationEnd pointer (count * 32)).toNat = pointer.toNat + count.toNat * 32 := by
  have product : (count * 32).toNat = count.toNat * 32 := by
    rw [BitVec.toNat_mul_of_lt (by change count.toNat * 32 < 2^64; omega)]
    rfl
  rw [allocationEnd_aligned_toNat pointer (count * 32) (by rw [product]; exact bounded)
    aligned (by rw [product]; omega),product]

/-- Exact frontier growth retains both earlier allocations and a remaining reserve. -/
theorem access_keys_heap_reserve (pointer count : BitVec 64) (reserve ceiling : Nat)
    (aligned : pointer.toNat % 8 = 0)
    (bounded : pointer.toNat + count.toNat * 32 ≤ 33806089496)
    (budget : pointer.toNat + count.toNat * 32 + reserve ≤ ceiling) :
    pointer.toNat ≤ (allocationEnd pointer (count * 32)).toNat ∧
      (allocationEnd pointer (count * 32)).toNat + reserve ≤ ceiling := by
  rw [access_keys_heap_advance pointer count aligned bounded]
  exact ⟨Nat.le_add_right _ _,budget⟩

#print axioms access_keys_heap_advance
#print axioms access_keys_heap_reserve
end InitECandidate.Runtime
