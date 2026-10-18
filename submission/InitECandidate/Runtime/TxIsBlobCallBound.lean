import InitECandidate.Runtime.OriginalTxIsBlobCode
import InitECandidate.Runtime.TxIsBlobBodyBound
import InitECandidate.Runtime.PanSingleWordLookup
import InitECandidate.Runtime.PanDecCallStraightBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_tx_is_blob_decCall_straight_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (argument : ExpHOL 64) (tx : BitVec 64) (continuation : ProgHOL 64)
    (supported : straightLine continuation = true) (code : state.code = originalRuntimeCode)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [argument] = some [.val (.word tx)]) (budget : 1 ≤ state.clock) :
    let output := evaluateHOLFiniteState state (.decCall name .one (ofString "tx_is_blob") [argument] continuation)
    state.clock ≤ output.2.clock + 1 ∧ output.2.clock ≤ state.clock ∧ output.1 ≠ some .timeOut := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "tx",.val (.word tx))
  let entry := callEntryStateHOLFinite state callee
  have bounded := evaluate_tx_is_blob_body_bounded entry
  cases run : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_tx_is_blob) with
  | mk result post =>
    rw [run] at bounded
    have lookup := pan_single_word_lookup state.code.lookup (ofString "tx_is_blob") (ofString "tx")
      (sourceFunctionBody Guest.guestFn_tx_is_blob) tx (by rw [code]; exact originalRuntimeCode_txIsBlob_lookup)
    apply evaluate_decCall_straight_bounded state post name (ofString "tx_is_blob") .one .one
      [argument] [.val (.word tx)] (sourceFunctionBody Guest.guestFn_tx_is_blob) continuation callee result 1 args lookup (by omega) run
    · exact Nat.le_of_eq bounded.1
    · have clock : post.clock = state.clock - 1 := bounded.1
      omega
    · exact bounded.2
    · exact supported

#print axioms evaluate_tx_is_blob_decCall_straight_bounded
end InitECandidate.Runtime
