import InitECandidate.Runtime.TransactionFeeLegacySuffixBound
import InitECandidate.Runtime.TransactionU256AtThenBound
import InitECandidate.Runtime.TransactionIndexAdd
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def transactionFeeDynamicSuffix : ProgHOL 64 :=
  .seq (transactionU256Field 80 (transactionFeeArguments 0))
    (.seq (transactionU256Field 112 (transactionFeeArguments 1))
      (.seq (transactionFeeAdvance 2) (transactionAt 23)))
theorem evaluate_transaction_fee_dynamic_suffix {F : Type} (state : PanSemStateFiniteExact 64 F) :
    evaluateHOLFiniteState state (.seq transactionFeeDynamic (transactionAt 23)) =
      evaluateHOLFiniteState state transactionFeeDynamicSuffix := by
  unfold transactionFeeDynamic transactionFeeDynamicSuffix transactionU256Field transactionFeeCall transactionFeeStore
  rw [evaluate_seq_assoc,evaluate_seq_assoc]
  apply evaluate_seq_second_congr
  intro current
  rw [evaluate_seq_assoc]
  apply evaluate_seq_second_congr
  intro next
  rw [evaluate_seq_assoc,evaluate_seq_assoc]
  apply evaluate_seq_second_congr
  intro final
  exact evaluate_seq_assoc final _ _ _

def transactionFeeDynamicSuffixCost (length : Nat) : Nat :=
  2 * (length * ((2 * length + 1) * 15 + 19) + 92668) + transactionGasSuffixCost length

theorem transaction_fee_dynamic_suffix_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
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
  apply transaction_u256_then_bounded state array count tx kind input inputLength scratch frame ceiling inputLimit
    valid 80 0 (transactionFeeArguments 0) args inside inputBound limitBound orderedFrame framePositive scratchBelow arrayBelow
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
      wordOpHOL,wordOp,valueIsWord,valueWord,show (1 : BitVec 64) ≠ 0 by decide]
  apply transaction_u256_at_then_bounded post array count tx kind input inputLength scratch frame ceiling inputLimit
    next 112 0 (next.index + 1) (transactionFeeArguments 1) secondArgs secondInside inputBound limitBound orderedFrame framePositive scratchBelow arrayBelow
    (by change tx.toNat + 112 + 24 < array.toNat; omega) _ (transactionGasSuffixCost inputLength.toNat) ticks
  intro final finished finalIndex finalHeap finalTicks
  have sameIndex : finished.index = valid.index := finalIndex.trans indexEqual
  have within : finished.index.toNat + (2 : BitVec 64).toNat ≤ count.toNat := by rw [sameIndex]; change valid.index.toNat + 2 ≤ count.toNat; omega
  let advanced := finished.addIndex 2 within
  have addTwo : (finished.index + 2).toNat = finished.index.toNat + 2 := by
    rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change finished.index.toNat + 2 < 2^64; rw [sameIndex]; omega)]
    rfl
  have remainingFields : advanced.index.toNat + 11 ≤ count.toNat := by
    change (finished.index + 2).toNat + 11 ≤ count.toNat
    rw [addTwo,sameIndex]; exact fields
  have remaining := transaction_gas_suffix_bounded _ array count tx kind input inputLength scratch frame ceiling inputLimit
    advanced remainingFields inputBound limitBound orderedFrame framePositive scratchBelow countLimit arrayBelow headerBefore
    (by change finished.heap.toNat + _ + _ + _ + 7 ≤ frame.toNat; rw [finalHeap,heapEqual]; exact reserve) finalTicks
  dsimp only
  change final.clock ≤ (evaluateHOLFiniteState final (.seq (transactionIndexAdd 2) (transactionAt 23))).2.clock + transactionGasSuffixCost inputLength.toNat ∧
    (evaluateHOLFiniteState final (.seq (transactionIndexAdd 2) (transactionAt 23))).2.clock ≤ final.clock ∧
    (evaluateHOLFiniteState final (.seq (transactionIndexAdd 2) (transactionAt 23))).1 ≠ some .timeOut
  rw [evaluateHOLFiniteState_seq_line780,transaction_index_add_run final finished.index 2 finished.indexLocal]
  exact remaining

#print axioms transaction_fee_dynamic_suffix_bounded
end InitECandidate.Runtime
