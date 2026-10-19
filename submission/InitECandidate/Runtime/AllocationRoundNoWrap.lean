import InitECandidate.Runtime.AllocationRound
namespace InitECandidate.Runtime
open Flapjack

/-- Rounded allocation coverage only needs a nonoverflowing padded sum. -/
theorem allocationEnd_covers_noWrap (pointer size : BitVec 64)
    (fits : pointer.toNat + size.toNat + 7 < 2^64) :
    pointer.toNat + size.toNat ≤ (allocationEnd pointer size).toNat := by
  have sumEq := BitVec.toNat_add_of_lt (by omega : pointer.toNat + size.toNat < 2^64)
  have padded : (pointer + size).toNat + (7 : BitVec 64).toNat < 2^64 := by
    rw [sumEq]
    exact fits
  have endpoint : (allocationEnd pointer size).toNat = (pointer.toNat + size.toNat + 7) / 8 * 8 := by
    rw [allocationEnd_eq_align,panByteAlign_toNat64,BitVec.toNat_add_of_lt padded,sumEq]
    rfl
  rw [endpoint]
  have division := Nat.mod_add_div (pointer.toNat + size.toNat + 7) 8
  have remainder := Nat.mod_lt (pointer.toNat + size.toNat + 7) (by decide : 0 < 8)
  omega

#print axioms allocationEnd_covers_noWrap
end InitECandidate.Runtime
