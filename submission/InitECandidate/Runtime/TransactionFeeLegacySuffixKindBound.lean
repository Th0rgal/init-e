import InitECandidate.Runtime.TransactionFeeLegacySuffixBound
import InitECandidate.Runtime.TransactionGasSuffixKindBound
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_fee_legacy_suffix_bounded_by_kind {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (fields : valid.index.toNat + (if kind = 0#64 then 0 else 1) + (if kind = 3#64 then 2 else 0) + (if kind = 4#64 then 1 else 0) + 8 ≤ count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 120 < 2^64)
    (arrayBelow : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (headerBefore : tx.toNat + 344 < array.toNat)
    (reserve : valid.heap.toNat + inputLength.toNat * 40 + (inputLength.toNat * 48 + 46) * inputLength.toNat + inputLength.toNat * 296 + 7 ≤ frame.toNat)
    (budget : transactionFeeLegacySuffixCost inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state transactionFeeLegacySuffix
    state.clock ≤ evaluated.2.clock + transactionFeeLegacySuffixCost inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have inside : valid.index.toNat < count.toNat := by omega
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) (transactionFeeArguments 0) =
      some [.val (.word array),.val (.word valid.index),.val (.word (0 : BitVec 64))] := by
    simp [transactionFeeArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,valid.arrayLocal,valid.indexLocal]
  unfold transactionFeeLegacySuffix
  apply transaction_u256_then_bounded state array count tx kind input inputLength scratch frame ceiling inputLimit
    valid 48 0 (transactionFeeArguments 0) args inside inputBound limitBound orderedFrame framePositive scratchBelow arrayBelow
    (by change tx.toNat + 48 + 24 < array.toNat; omega) _ (transactionGasSuffixCost inputLength.toNat) budget
  intro post next indexEqual heapEqual ticks
  have nextInside : next.index.toNat < count.toNat := by rw [indexEqual]; omega
  let advanced := next.advanceIndex nextInside
  have addOne : (next.index + 1).toNat = next.index.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change next.index.toNat + 1 < 2^64; omega)]
    rfl
  have remainingFields : advanced.index.toNat + (if kind = 0#64 then 0 else 1) + (if kind = 3#64 then 2 else 0) + (if kind = 4#64 then 1 else 0) + 7 ≤ count.toNat := by
    change (next.index + 1).toNat + (if kind = 0#64 then 0 else 1) + (if kind = 3#64 then 2 else 0) + (if kind = 4#64 then 1 else 0) + 7 ≤ count.toNat
    rw [addOne,indexEqual]; omega
  have remaining := transaction_gas_suffix_bounded_by_kind _ array count tx kind input inputLength scratch frame ceiling inputLimit
    advanced remainingFields inputBound limitBound orderedFrame framePositive scratchBelow countLimit arrayBelow headerBefore
    (by change next.heap.toNat + _ + _ + _ + 7 ≤ frame.toNat; rw [heapEqual]; exact reserve) ticks
  dsimp only
  change post.clock ≤ (evaluateHOLFiniteState post (.seq transactionIndexAdvance (transactionAt 23))).2.clock + transactionGasSuffixCost inputLength.toNat ∧
    (evaluateHOLFiniteState post (.seq transactionIndexAdvance (transactionAt 23))).2.clock ≤ post.clock ∧
    (evaluateHOLFiniteState post (.seq transactionIndexAdvance (transactionAt 23))).1 ≠ some .timeOut
  rw [evaluateHOLFiniteState_seq_line780,transaction_index_advance_run post next.index next.indexLocal]
  exact remaining

#print axioms transaction_fee_legacy_suffix_bounded_by_kind
end InitECandidate.Runtime
