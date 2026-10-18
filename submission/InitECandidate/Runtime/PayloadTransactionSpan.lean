import InitECandidate.Runtime.PayloadOffsetBounds
namespace InitECandidate.Runtime
open Flapjack

/-- Ordered accepted offsets produce the exact transaction byte span inside
the original input, without wrapping either pointer addition or subtraction. -/
theorem payload_transaction_span (input length transactions withdrawals : BitVec 64)
    (ordered : transactions.toNat ≤ withdrawals.toNat)
    (within : withdrawals.toNat ≤ length.toNat)
    (inputFits : input.toNat + length.toNat < 2 ^ 64) :
    (withdrawals - transactions).toNat = withdrawals.toNat - transactions.toNat ∧
      (input + transactions).toNat = input.toNat + transactions.toNat ∧
      (input + transactions).toNat + (withdrawals - transactions).toNat ≤ input.toNat + length.toNat ∧
      (withdrawals - transactions).toNat ≤ length.toNat := by
  have unsigned : transactions ≤ withdrawals := by change transactions.toNat ≤ withdrawals.toNat; exact ordered
  have difference := BitVec.toNat_sub_of_le unsigned
  have pointer := BitVec.toNat_add_of_lt (x := input) (y := transactions) (by omega)
  refine ⟨difference,pointer,?_,?_⟩
  · rw [difference,pointer]
    omega
  · rw [difference]
    omega

#print axioms payload_transaction_span
end InitECandidate.Runtime
