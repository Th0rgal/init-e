import InitECandidate.Runtime.TransactionWrapperCallBound
import InitECandidate.Runtime.AccessListCostMonotone
import InitECandidate.Runtime.BlobHashesCostMonotone
import InitECandidate.Runtime.AuthorizationsCostMonotone
set_option maxRecDepth 100000
set_option maxHeartbeats 100000
namespace InitECandidate.Runtime

/-- A containing inputs length supplies a uniform budget for every nested transaction. -/
theorem transaction_wrapper_call_cost_mono (left right : Nat) (bounded : left ≤ right) :
    transactionWrapperCallCost left ≤ transactionWrapperCallCost right := by
  have factor : (2 * left + 1) * 15 + 19 ≤ (2 * right + 1) * 15 + 19 := by omega
  have quadratic := Nat.mul_le_mul bounded factor
  have bytes := Nat.mul_le_mul_right 12 bounded
  have access := accessBodyCost_mono (first := left) (second := right) bounded
  have blob := blobHashesBodyCost_mono (first := left) (second := right) bounded
  have authorization := authorizationBodyCost_mono (first := left) (second := right) bounded
  simp only [transactionWrapperCallCost,transactionCallCost,transactionAllocationSuffixCost,
    transactionMemzeroSuffixCost,transactionTypedSuffixCost,transactionListSuffixCost,
    transactionChainIdSuffixCost,transactionNonceSuffixCost,transactionFeeDynamicSuffixCost,
    transactionGasSuffixCost,transactionToSuffixCost,transactionValueSuffixCost,transactionDataSequenceCost,
    transactionTypedSignatureCost,transactionBlobSignatureCost,transactionAuthorizationSignatureCost,
    txListItemAccessCost,txListItemBlobCost,txListItemAuthorizationCost]
  exact (Nat.add_le_add (Nat.le_refl 1) (Nat.add_le_add (Nat.le_refl 1) (Nat.add_le_add (Nat.le_refl 1) (Nat.add_le_add (Nat.le_refl 401) (Nat.add_le_add (Nat.add_le_add quadratic (Nat.le_refl 92635)) (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add quadratic bytes) (Nat.le_refl 4)) (Nat.add_le_add (Nat.add_le_add quadratic (Nat.le_refl 92643)) (Nat.add_le_add (Nat.add_le_add quadratic (Nat.le_refl 92668)) (Nat.add_le_add (Nat.mul_le_mul (Nat.le_refl 2) (Nat.add_le_add quadratic (Nat.le_refl 92668))) (Nat.add_le_add (Nat.add_le_add quadratic (Nat.le_refl 92643)) (Nat.add_le_add (Nat.add_le_add quadratic (Nat.le_refl 92634)) (Nat.add_le_add (Nat.add_le_add quadratic (Nat.le_refl 92668)) (Nat.add_le_add (Nat.add_le_add quadratic (Nat.le_refl 92634)) (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add quadratic (Nat.le_refl 92634)) (Nat.add_le_add access (Nat.le_refl 1))) (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add quadratic (Nat.le_refl 92668)) (Nat.add_le_add (Nat.add_le_add quadratic (Nat.le_refl 92634)) (Nat.add_le_add blob (Nat.le_refl 1)))) (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add quadratic (Nat.le_refl 92634)) (Nat.add_le_add authorization (Nat.le_refl 1))) (Nat.mul_le_mul (Nat.le_refl 3) (Nat.add_le_add quadratic (Nat.le_refl 92668)))))))))))))))))))

#print axioms transaction_wrapper_call_cost_mono
end InitECandidate.Runtime
