import InitECandidate.Runtime.TransactionSignatureMiddleBound
import InitECandidate.Runtime.TransactionSignatureLastHeapOuterPrefix
import InitECandidate.Runtime.TransactionU256FieldHeapRuntimeFrame
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_signature_middle_returned_heap_outer_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count index tx input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : (index + 2#64).toNat < count.toNat)
    (middleInside : (index + 1#64).toNat < count.toNat)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (before : tx.toNat + 320 + 24 < array.toNat)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : 2 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ≤ state.clock)
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerFits : outerArray.toNat + outerCount.toNat * 16 ≤ 2^64)
    (outerAbove : ceiling ≤ outerArray.toNat)
    (beforeTx : outerArray.toNat + outerCount.toNat * 16 ≤ tx.toNat)
    (fits : tx.toNat + 352 + 24 < 2^64)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state transactionSignatureMiddle = (some (.returned value),post)) :
    RlpSliceInputPrefix post outerArray outerInput outerLength outerCount.toNat := by
  let cost := inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668
  have firstBudget : cost ≤ state.clock := by dsimp [cost]; omega
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) transactionSignatureMiddleArguments =
      some [.val (.word array),.val (.word (index + 1#64)),.val (.word (32 : BitVec 64))] := by
    simp [transactionSignatureMiddleArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_transaction_signature_middle,← evaluate_seq_assoc] at run
  change evaluateHOLFiniteState state (.seq transactionSignatureMiddleField transactionSignatureLast) = _ at run
  rw [evaluateHOLFiniteState_seq_line780] at run
  have noReturn := evaluate_noDirectReturn transactionSignatureMiddleField (by rfl) state value
  cases firstRun : evaluateHOLFiniteState state transactionSignatureMiddleField with
  | mk result middle =>
    rw [firstRun] at run noReturn
    cases result with
    | some result => exact False.elim (noReturn (Prod.mk.inj run).1)
    | none =>
      have kept := transaction_u256_field_normal_heap_runtime_frame state middle tx 320 transactionSignatureMiddleArguments
        array (index + 1#64) 32 input inputLength scratch frame count ceiling inputLimit args valid middleInside inputBound limitBound
        scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena firstBudget arrayFits arrayAbove txLocal before
        outerArray outerCount outerInput outerLength outerValid outerFits outerAbove beforeTx firstRun
      exact transaction_signature_last_returned_heap_outer_prefix middle post array index input inputLength scratch frame count.toNat ceiling inputLimit count.isLt
        ((kept.2.2.2.1 _ (by decide)).trans arrayLocal) ((kept.2.2.2.1 _ (by decide)).trans indexLocal)
        kept.1 inside inputBound limitBound ((kept.2.2.1 _).trans scratchGlobal) ((kept.2.2.1 _).trans frameGlobal)
        (kept.2.2.2.2.1.trans code) orderedFrame framePositive scratchBelow
        (by intro address lower upper; rw [kept.2.2.2.2.2.1]; exact arena address lower upper)
        (by have spent := kept.2.2.2.2.2.2.1; dsimp [cost] at firstBudget; omega)
        tx outerArray outerCount outerInput outerLength ((kept.2.2.2.1 _ (by decide)).trans txLocal)
        kept.2.1 outerFits outerAbove beforeTx fits value run

#print axioms transaction_signature_middle_returned_heap_outer_prefix
end InitECandidate.Runtime
