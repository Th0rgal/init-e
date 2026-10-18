import InitECandidate.Runtime.TransactionSignatureFirstBound
import InitECandidate.Runtime.TransactionSignatureMiddleHeapBound
import InitECandidate.Runtime.TransactionU256FieldBound
import InitECandidate.Runtime.TransactionU256FieldHeapFrame
import InitECandidate.Runtime.PanSeqAssoc
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The three original signature fields share a three-call clock budget. -/
theorem evaluate_transaction_signature_first_heap_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count index tx input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : (index + 2#64).toNat < count.toNat)
    (middleInside : (index + 1#64).toNat < count.toNat)
    (firstInside : index.toNat < count.toNat)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (before : tx.toNat + 320 + 24 < array.toNat)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : 3 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state transactionSignatureFirst
    state.clock ≤ evaluated.2.clock + 3 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let cost := inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) transactionSignatureFirstArguments =
      some [.val (.word array),.val (.word index),.val (.word (32 : BitVec 64))] := by
    simp [transactionSignatureFirstArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal]
  have firstBudget : cost ≤ state.clock := by dsimp [cost]; omega
  have bounded := evaluate_transaction_u256_field_bounded state (ofString "v")
    (.op .add [.var .local (ofString "tx"),.const 288]) transactionSignatureFirstArguments
    array index 32 input inputLength scratch frame count.toNat ceiling inputLimit args valid firstInside inputBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena firstBudget
  change state.clock ≤ (evaluateHOLFiniteState state transactionSignatureFirstField).2.clock + cost ∧
    (evaluateHOLFiniteState state transactionSignatureFirstField).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState state transactionSignatureFirstField).1 ≠ some .timeOut at bounded
  rw [source_transaction_signature_first,← evaluate_seq_assoc]
  change state.clock ≤ (evaluateHOLFiniteState state (.seq transactionSignatureFirstField transactionSignatureMiddle)).2.clock + 3 * cost ∧
    (evaluateHOLFiniteState state (.seq transactionSignatureFirstField transactionSignatureMiddle)).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState state (.seq transactionSignatureFirstField transactionSignatureMiddle)).1 ≠ some .timeOut
  simp only [evaluateHOLFiniteState_seq_line780 state transactionSignatureFirstField transactionSignatureMiddle]
  cases firstRun : evaluateHOLFiniteState state transactionSignatureFirstField with
  | mk result middle =>
    rw [firstRun] at bounded
    dsimp only at bounded ⊢
    cases result with
    | some result =>
      dsimp only
      exact ⟨by omega,bounded.2.1,bounded.2.2⟩
    | none =>
      dsimp only
      have kept := transaction_u256_field_normal_heap_frame state middle tx 288 transactionSignatureFirstArguments array index 32
        input inputLength scratch frame count ceiling inputLimit args valid firstInside inputBound limitBound scratchGlobal frameGlobal code
        orderedFrame framePositive scratchBelow arena firstBudget arrayFits arrayAbove txLocal (by change tx.toNat + 288 + 24 < array.toNat; omega) firstRun
      have metadata := evaluateHOLFiniteState_metadata state transactionSignatureFirstField
      rw [firstRun] at metadata
      have tail := evaluate_transaction_signature_middle_heap_bounded middle array count index tx input inputLength scratch frame ceiling inputLimit
        ((kept.2.2 _ (by decide)).trans arrayLocal) ((kept.2.2 _ (by decide)).trans indexLocal)
        kept.1 inside middleInside
        ((kept.2.2 _ (by decide)).trans txLocal) (by omega) arrayFits arrayAbove inputBound limitBound ((kept.2.1 _).trans scratchGlobal) ((kept.2.1 _).trans frameGlobal)
        (metadata.1.trans code) orderedFrame framePositive scratchBelow
        (by intro address lower upper; rw [metadata.2.1]; exact arena address lower upper)
        (transaction_signature_remaining_budget cost state.clock middle.clock budget bounded.1)
      exact ⟨by dsimp [cost] at bounded ⊢; omega,Nat.le_trans tail.2.1 bounded.2.1,tail.2.2⟩

#print axioms evaluate_transaction_signature_first_heap_bounded
end InitECandidate.Runtime
