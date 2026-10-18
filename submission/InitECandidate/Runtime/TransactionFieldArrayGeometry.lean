import InitECandidate.Runtime.AllocationAligned
namespace InitECandidate.Runtime
open Flapjack

/-- The aligned transaction header and its 16-byte field entries require no
allocator padding. This supplies the concrete heap geometry for later fields. -/
theorem transaction_field_array_heap_geometry (tx count : BitVec 64)
    (space : tx.toNat + 400 + count.toNat * 16 ≤ 33806089496)
    (aligned : tx.toNat % 8 = 0) :
    (allocationEnd tx 400).toNat = tx.toNat + 400 ∧
      (count * 16).toNat = count.toNat * 16 ∧
      (allocationEnd (allocationEnd tx 400) (count * 16)).toNat = tx.toNat + 400 + count.toNat * 16 ∧
      (allocationEnd (allocationEnd tx 400) (count * 16)).toNat % 8 = 0 ∧
      (allocationEnd (allocationEnd tx 400) (count * 16)).toNat ≤ 33806089496 := by
  have header : (allocationEnd tx 400).toNat = tx.toNat + 400 :=
    allocationEnd_aligned_toNat tx 400 (by change tx.toNat + 400 ≤ 33806089496; omega) aligned (by decide)
  have request : (allocationEnd tx 400).toNat + count.toNat * (16 : BitVec 64).toNat ≤ 33806089496 := by
    change (allocationEnd tx 400).toNat + count.toNat * 16 ≤ 33806089496
    rw [header]
    exact space
  have product := (allocation_product_request (allocationEnd tx 400) count 16 request).1
  change (count * 16).toNat = count.toNat * 16 at product
  have endpoint := allocationEnd_aligned_toNat (allocationEnd tx 400) (count * 16)
    (by rw [product]; exact request)
    (by rw [header]; omega)
    (by rw [product]; omega)
  rw [header,product] at endpoint
  exact ⟨header,product,endpoint,by rw [endpoint]; omega,by rw [endpoint]; exact space⟩

#print axioms transaction_field_array_heap_geometry
end InitECandidate.Runtime
