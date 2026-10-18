import InitECandidate.Runtime.TransactionListSuffixBound
namespace InitECandidate.Runtime

theorem transaction_list_suffix_cost_mono (left right inputLength : Nat) (bounded : left ≤ right) :
    transactionListSuffixCost left inputLength ≤ transactionListSuffixCost right inputLength := by
  have factor : (2 * left + 1) * 15 + 19 ≤ (2 * right + 1) * 15 + 19 := by omega
  have product := Nat.mul_le_mul bounded factor
  unfold transactionListSuffixCost
  omega

#print axioms transaction_list_suffix_cost_mono
end InitECandidate.Runtime
