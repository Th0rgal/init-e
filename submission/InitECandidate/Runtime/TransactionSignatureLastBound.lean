import InitECandidate.Runtime.TransactionDecoderSource
import InitECandidate.Runtime.TxScalarU256CallInputBound
import InitECandidate.Runtime.PanSeqStraightBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A transaction scalar assignment followed by its header store shares the call budget,
including call rejection, failed assignment and inaccessible header stores. -/
theorem evaluate_transaction_signature_last_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array index input inputLength scratch frame : BitVec 64) (filled ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (valid : RlpSliceInputPrefix state array input inputLength filled) (inside : (index + 2#64).toNat < filled)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state transactionSignatureLast
    state.clock ≤ evaluated.2.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) transactionSignatureLastArguments =
      some [.val (.word array),.val (.word (index + 2#64)),.val (.word (32 : BitVec 64))] := by
    simp [transactionSignatureLastArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  have bound := evaluate_txScalarU256_call_input_bounded state (some (.local,ofString "v")) transactionSignatureLastArguments
    array (index + 2#64) 32 input inputLength scratch frame filled ceiling inputLimit args valid inside inputBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
  rw [source_transaction_signature_last]
  exact evaluate_sequence_straight_bounded state _ transactionSignatureLastTail _ bound (by rfl)

#print axioms evaluate_transaction_signature_last_bounded
end InitECandidate.Runtime
