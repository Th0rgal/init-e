import InitECandidate.Runtime.TransactionSignatureFirstBound
import InitECandidate.Runtime.TransactionSignatureMiddleOuterPrefix
import InitECandidate.Runtime.TransactionU256FieldRuntimeFrame
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_signature_first_returned_outer_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count index tx input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : (index + 2#64).toNat < count.toNat)
    (middleInside : (index + 1#64).toNat < count.toNat)
    (firstInside : index.toNat < count.toNat)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (before : tx.toNat + 320 + 24 < array.toNat)
    (arrayBelow : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : 3 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ≤ state.clock)
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerBelow : outerArray.toNat + outerCount.toNat * 16 ≤ frame.toNat)
    (beforeTx : outerArray.toNat + outerCount.toNat * 16 ≤ tx.toNat)
    (fits : tx.toNat + 352 + 24 < 2^64)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state transactionSignatureFirst = (some (.returned value),post)) :
    RlpSliceInputPrefix post outerArray outerInput outerLength outerCount.toNat := by
  let cost := inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668
  have firstBudget : cost ≤ state.clock := by dsimp [cost]; omega
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) transactionSignatureFirstArguments =
      some [.val (.word array),.val (.word index),.val (.word (32 : BitVec 64))] := by
    simp [transactionSignatureFirstArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal]
  rw [source_transaction_signature_first,← evaluate_seq_assoc] at run
  change evaluateHOLFiniteState state (.seq transactionSignatureFirstField transactionSignatureMiddle) = _ at run
  rw [evaluateHOLFiniteState_seq_line780] at run
  have noReturn := evaluate_noDirectReturn transactionSignatureFirstField (by rfl) state value
  cases firstRun : evaluateHOLFiniteState state transactionSignatureFirstField with
  | mk result middle =>
    rw [firstRun] at run noReturn
    cases result with
    | some result => exact False.elim (noReturn (Prod.mk.inj run).1)
    | none =>
      have kept := transaction_u256_field_normal_runtime_frame state middle tx 288 transactionSignatureFirstArguments
        array index 32 input inputLength scratch frame count ceiling inputLimit args valid firstInside inputBound limitBound
        scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena firstBudget arrayBelow txLocal (by change tx.toNat + 288 + 24 < array.toNat; omega)
        outerArray outerCount outerInput outerLength outerValid outerBelow beforeTx firstRun
      exact transaction_signature_middle_returned_outer_prefix middle post array count index tx input inputLength scratch frame ceiling inputLimit
        ((kept.2.2.2.1 _ (by decide)).trans arrayLocal) ((kept.2.2.2.1 _ (by decide)).trans indexLocal)
        kept.1 inside middleInside ((kept.2.2.2.1 _ (by decide)).trans txLocal) before arrayBelow
        inputBound limitBound ((kept.2.2.1 _).trans scratchGlobal) ((kept.2.2.1 _).trans frameGlobal)
        (kept.2.2.2.2.1.trans code) orderedFrame framePositive scratchBelow
        (by intro address lower upper; rw [kept.2.2.2.2.2.1]; exact arena address lower upper)
        (transaction_signature_remaining_budget cost state.clock middle.clock budget kept.2.2.2.2.2.2.1)
        outerArray outerCount outerInput outerLength kept.2.1 outerBelow beforeTx fits value run

#print axioms transaction_signature_first_returned_outer_prefix
end InitECandidate.Runtime
