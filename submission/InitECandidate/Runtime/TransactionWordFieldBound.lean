import InitECandidate.Runtime.TxScalarWordCallInputBound
import InitECandidate.Runtime.PanSeqStraightBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A transaction scalar assignment followed by its header store shares the call budget,
including call rejection, failed assignment and inaccessible header stores. -/
theorem evaluate_transaction_word_field_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (destination : ExpHOL 64) (arguments : List (ExpHOL 64))
    (array index maximum errorCode input inputLength scratch frame : BitVec 64) (filled ceiling inputLimit : Nat)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word array),.val (.word index),.val (.word maximum),.val (.word errorCode)])
    (valid : RlpSliceInputPrefix state array input inputLength filled) (inside : index.toNat < filled)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92643 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.seq (.call (some (some (.local,name),none)) (ofString "tx_scalar_word") arguments) (.store destination (.var .local name)))
    state.clock ≤ evaluated.2.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92643) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have bound := evaluate_txScalarWord_call_input_bounded state (some (.local,name)) arguments
    array index maximum errorCode input inputLength scratch frame filled ceiling inputLimit args valid inside inputBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
  exact evaluate_sequence_straight_bounded state
    (.call (some (some (.local,name),none)) (ofString "tx_scalar_word") arguments)
    (.store destination (.var .local name)) _ bound (by rfl)

#print axioms evaluate_transaction_word_field_bounded
end InitECandidate.Runtime
