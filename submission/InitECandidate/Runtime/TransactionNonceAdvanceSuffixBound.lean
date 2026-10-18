import InitECandidate.Runtime.TransactionFeeSuffixBound
import InitECandidate.Runtime.TransactionIndexAdvance
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_transaction_nonce_advance : transactionAt 21 = .seq transactionIndexAdvance (transactionAt 22) := by
  simp only [transactionIndexAdvance,transactionAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem transaction_nonce_advance_suffix_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (fields : valid.index.toNat + 14 ≤ count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 120 < 2^64)
    (arrayBelow : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (headerBefore : tx.toNat + 344 < array.toNat)
    (reserve : valid.heap.toNat + inputLength.toNat * 40 + (inputLength.toNat * 48 + 46) * inputLength.toNat + inputLength.toNat * 296 + 7 ≤ frame.toNat)
    (budget : transactionFeeDynamicSuffixCost inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (transactionAt 21)
    state.clock ≤ evaluated.2.clock + transactionFeeDynamicSuffixCost inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have inside : valid.index.toNat < count.toNat := by omega
  let next := valid.advanceIndex inside
  have addOne : (valid.index + 1).toNat = valid.index.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change valid.index.toNat + 1 < 2^64; omega)]
    rfl
  have nextFields : next.index.toNat + 13 ≤ count.toNat := by
    change (valid.index + 1).toNat + 13 ≤ count.toNat
    rw [addOne]; omega
  have bounded := transaction_fee_suffix_bounded _ array count tx kind input inputLength scratch frame ceiling inputLimit
    next nextFields inputBound limitBound orderedFrame framePositive scratchBelow countLimit arrayBelow headerBefore reserve budget
  rw [source_transaction_nonce_advance,evaluateHOLFiniteState_seq_line780,transaction_index_advance_run state valid.index valid.indexLocal]
  dsimp only
  exact bounded

#print axioms transaction_nonce_advance_suffix_bounded
end InitECandidate.Runtime
