import InitECandidate.Runtime.TransactionU256HeapContinuationBound
import InitECandidate.Runtime.TransactionU256AtThenHeapBound
import InitECandidate.Runtime.TransactionFeeDynamicSuffixBound
import InitECandidate.Runtime.TransactionGasSuffixHeapKindBound
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_fee_dynamic_suffix_heap_bounded_by_kind {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (fields : valid.index.toNat + (if kind = 0#64 then 0 else 1) + (if kind = 3#64 then 2 else 0) + (if kind = 4#64 then 1 else 0) + 9 ≤ count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 120 < 2^64)
    (arrayAbove : ceiling ≤ array.toNat)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (headerBefore : tx.toNat + 344 < array.toNat)
    (budget : transactionFeeDynamicSuffixCost inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state transactionFeeDynamicSuffix
    state.clock ≤ evaluated.2.clock + transactionFeeDynamicSuffixCost inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let cost := inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668
  have inside : valid.index.toNat < count.toNat := by omega
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) (transactionFeeArguments 0) =
      some [.val (.word array),.val (.word valid.index),.val (.word (0 : BitVec 64))] := by
    simp [transactionFeeArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,valid.arrayLocal,valid.indexLocal]
  have costEq : transactionFeeDynamicSuffixCost inputLength.toNat = cost + (cost + transactionGasSuffixCost inputLength.toNat) := by
    change 2 * cost + _ = cost + (cost + _)
    omega
  rw [costEq]
  unfold transactionFeeDynamicSuffix
  apply transaction_u256_heap_continuation_bounded state array count tx kind input inputLength scratch frame ceiling inputLimit
    valid 80 0 (transactionFeeArguments 0) args inside inputBound limitBound orderedFrame framePositive scratchBelow (by have h := valid.arrayBeforeHeap; omega) arrayAbove
    (by change tx.toNat + 80 + 24 < array.toNat; omega) _ (cost + transactionGasSuffixCost inputLength.toNat)
    (by change 2 * cost + _ ≤ state.clock at budget; omega)
  intro post next indexEqual heapEqual ticks
  have addOne : (next.index + 1).toNat = next.index.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change next.index.toNat + 1 < 2^64; rw [indexEqual]; omega)]
    rfl
  have secondInside : (next.index + 1).toNat < count.toNat := by rw [addOne,indexEqual]; omega
  have secondArgs : evalListHOLFinite post (h := fun a => Classical.propDecidable (post.memaddrs a)) (transactionFeeArguments 1) =
      some [.val (.word array),.val (.word (next.index + 1)),.val (.word (0 : BitVec 64))] := by
    simp [transactionFeeArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,next.arrayLocal,next.indexLocal,
      wordOpHOL,wordOp,valueIsWord,valueWord]
  apply transaction_u256_at_then_heap_bounded post array count tx kind input inputLength scratch frame ceiling inputLimit
    next 112 0 (next.index + 1) (transactionFeeArguments 1) secondArgs secondInside inputBound limitBound orderedFrame framePositive scratchBelow (by have h := valid.arrayBeforeHeap; omega) arrayAbove
    (by change tx.toNat + 112 + 24 < array.toNat; omega) _ (transactionGasSuffixCost inputLength.toNat) ticks
  intro final finished finalIndex finalHeap finalTicks
  have sameIndex : finished.index = valid.index := finalIndex.trans indexEqual
  have within : finished.index.toNat + (2 : BitVec 64).toNat ≤ count.toNat := by rw [sameIndex]; change valid.index.toNat + 2 ≤ count.toNat; omega
  let advanced := finished.addIndex 2 within
  have addTwo : (finished.index + 2).toNat = finished.index.toNat + 2 := by
    rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change finished.index.toNat + 2 < 2^64; rw [sameIndex]; omega)]
    rfl
  have remainingFields : advanced.index.toNat + (if kind = 0#64 then 0 else 1) + (if kind = 3#64 then 2 else 0) + (if kind = 4#64 then 1 else 0) + 7 ≤ count.toNat := by
    change (finished.index + 2).toNat + (if kind = 0#64 then 0 else 1) + (if kind = 3#64 then 2 else 0) + (if kind = 4#64 then 1 else 0) + 7 ≤ count.toNat
    rw [addTwo,sameIndex]; omega
  have remaining := transaction_gas_suffix_heap_bounded_by_kind _ array count tx kind input inputLength scratch frame ceiling inputLimit
    advanced remainingFields inputBound limitBound orderedFrame framePositive scratchBelow countLimit arrayAbove inputBeforeFrame headerBefore
    finalTicks
  dsimp only
  change final.clock ≤ (evaluateHOLFiniteState final (.seq (transactionIndexAdd 2) (transactionAt 23))).2.clock + transactionGasSuffixCost inputLength.toNat ∧
    (evaluateHOLFiniteState final (.seq (transactionIndexAdd 2) (transactionAt 23))).2.clock ≤ final.clock ∧
    (evaluateHOLFiniteState final (.seq (transactionIndexAdd 2) (transactionAt 23))).1 ≠ some .timeOut
  rw [evaluateHOLFiniteState_seq_line780,transaction_index_add_run final finished.index 2 finished.indexLocal]
  exact remaining

#print axioms transaction_fee_dynamic_suffix_heap_bounded_by_kind
end InitECandidate.Runtime
