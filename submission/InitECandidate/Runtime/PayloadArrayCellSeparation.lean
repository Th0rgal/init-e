import InitECandidate.Runtime.PayloadTransactionSuffixMemoryFrame
namespace InitECandidate.Runtime
open Flapjack

/-- A slice cell in a real heap-bounded array above the payload allocation
cannot alias any payload header word. All additions/products are exact. -/
theorem payload_array_cell_separate (payload array count index cellOffset storeOffset : BitVec 64)
    (afterHeader : payload.toNat + 136 ≤ array.toNat)
    (arrayBound : array.toNat + count.toNat * 16 ≤ 33806089496)
    (inside : index.toNat < count.toNat) (cellSmall : cellOffset.toNat ≤ 8)
    (storeSmall : storeOffset.toNat ≤ 128) :
    array + index * 16 + cellOffset ≠ payload + storeOffset := by
  have product : (index * 16).toNat = index.toNat * 16 := by
    apply BitVec.toNat_mul_of_lt
    change index.toNat * 16 < 2 ^ 64
    omega
  have base : (array + index * 16).toNat = array.toNat + index.toNat * 16 := by
    have sum := BitVec.toNat_add_of_lt (x := array) (y := index * 16) (by rw [product]; omega)
    simpa only [product] using sum
  have cell : (array + index * 16 + cellOffset).toNat = array.toNat + index.toNat * 16 + cellOffset.toNat := by
    have sum := BitVec.toNat_add_of_lt (x := array + index * 16) (y := cellOffset) (by rw [base]; omega)
    simpa only [base] using sum
  have header : (payload + storeOffset).toNat = payload.toNat + storeOffset.toNat :=
    BitVec.toNat_add_of_lt (by omega)
  intro equal
  have same := congrArg BitVec.toNat equal
  rw [cell,header] at same
  omega

#print axioms payload_array_cell_separate
end InitECandidate.Runtime
