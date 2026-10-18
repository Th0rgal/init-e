import InitECandidate.Runtime.TransactionFeeDynamicSuffixBound
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_fee_suffix_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (fields : valid.index.toNat + 13 ≤ count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 120 < 2^64)
    (arrayBelow : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (headerBefore : tx.toNat + 344 < array.toNat)
    (reserve : valid.heap.toNat + inputLength.toNat * 40 + (inputLength.toNat * 48 + 46) * inputLength.toNat + inputLength.toNat * 296 + 7 ≤ frame.toNat)
    (budget : transactionFeeDynamicSuffixCost inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (transactionAt 22)
    state.clock ≤ evaluated.2.clock + transactionFeeDynamicSuffixCost inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have legacyBudget : transactionFeeLegacySuffixCost inputLength.toNat ≤ state.clock := by
    dsimp [transactionFeeLegacySuffixCost,transactionFeeDynamicSuffixCost] at *
    omega
  have legacy := transaction_fee_legacy_suffix_bounded state array count tx kind input inputLength scratch frame ceiling inputLimit
    valid (by omega) inputBound limitBound orderedFrame framePositive scratchBelow countLimit arrayBelow headerBefore reserve legacyBudget
  rw [← evaluate_transaction_fee_legacy_suffix] at legacy
  have dynamic := transaction_fee_dynamic_suffix_bounded state array count tx kind input inputLength scratch frame ceiling inputLimit
    valid fields inputBound limitBound orderedFrame framePositive scratchBelow countLimit arrayBelow headerBefore reserve budget
  rw [← evaluate_transaction_fee_dynamic_suffix] at dynamic
  have costLe : transactionFeeLegacySuffixCost inputLength.toNat ≤ transactionFeeDynamicSuffixCost inputLength.toNat := by
    dsimp [transactionFeeLegacySuffixCost,transactionFeeDynamicSuffixCost]; omega
  have legacyLarge : state.clock ≤ (evaluateHOLFiniteState state (.seq transactionFeeLegacy (transactionAt 23))).2.clock + transactionFeeDynamicSuffixCost inputLength.toNat ∧
      (evaluateHOLFiniteState state (.seq transactionFeeLegacy (transactionAt 23))).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state (.seq transactionFeeLegacy (transactionAt 23))).1 ≠ some .timeOut :=
    ⟨by have spent := legacy.1; omega,legacy.2.1,legacy.2.2⟩
  rw [source_transaction_fee]
  unfold transactionFeeBranch
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
  split
  · split
    · simpa only [evaluateHOLFiniteState_seq_line780] using dynamic
    · simpa only [evaluateHOLFiniteState_seq_line780] using legacyLarge
  · dsimp only; exact ⟨by omega,Nat.le_refl _,by simp⟩

#print axioms transaction_fee_suffix_bounded
end InitECandidate.Runtime
