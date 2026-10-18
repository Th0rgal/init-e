import InitECandidate.Runtime.TxIsBlobCallBound
import InitECandidate.Runtime.PanDecCallCheckedContinuationBound
import InitECandidate.Runtime.PanSeqStraightBound
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def versionedHashesScanTail : ProgHOL 64 :=
  .seq versionedHashesScan (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1]))

/-- The actual type test followed by the scan and transaction-index increment
has a finite uniform bound, including every exceptional exit. -/
theorem evaluate_versioned_hashes_typed_scan_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (tx vh cursor : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (vhLocal : state.locals.lookup (ofString "vh") = some (.val (.word vh)))
    (cursorLocal : state.locals.lookup (ofString "k") = some (.val (.word cursor)))
    (code : state.code = originalRuntimeCode) (budget : 1 + versionedHashesScanCost ≤ state.clock) :
    let output := evaluateHOLFiniteState state (.decCall (ofString "isb") .one (ofString "tx_is_blob")
      [.var .local (ofString "tx")] versionedHashesScanTail)
    state.clock ≤ output.2.clock + (1 + versionedHashesScanCost) ∧ output.2.clock ≤ state.clock ∧ output.1 ≠ some .timeOut := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "tx",.val (.word tx))
  let entry := callEntryStateHOLFinite state callee
  have bounded := evaluate_tx_is_blob_body_bounded entry
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_tx_is_blob)
  cases run : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_tx_is_blob) with
  | mk result post =>
    rw [run] at bounded metadata
    have clock : post.clock = state.clock - 1 := bounded.1
    have lookup := pan_single_word_lookup state.code.lookup (ofString "tx_is_blob") (ofString "tx")
      (sourceFunctionBody Guest.guestFn_tx_is_blob) tx (by rw [code]; exact originalRuntimeCode_txIsBlob_lookup)
    apply evaluate_decCall_checked_continuation_bounded state post (ofString "isb") (ofString "tx_is_blob") .one .one
      [.var .local (ofString "tx")] [.val (.word tx)] (sourceFunctionBody Guest.guestFn_tx_is_blob)
      versionedHashesScanTail callee result 1 versionedHashesScanCost
      (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,txLocal]) lookup (by omega) run
      (Nat.le_of_eq bounded.1) (by omega) bounded.2
    intro value returned checked
    let resumed := setVarHOLFinite (ofString "isb") value {post with locals := state.locals}
    have txResumed : resumed.locals.lookup (ofString "tx") = some (.val (.word tx)) := by
      simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
        show ofString "isb" ≠ ofString "tx" by decide] using txLocal
    have vhResumed : resumed.locals.lookup (ofString "vh") = some (.val (.word vh)) := by
      simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
        show ofString "isb" ≠ ofString "vh" by decide] using vhLocal
    have cursorResumed : resumed.locals.lookup (ofString "k") = some (.val (.word cursor)) := by
      simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
        show ofString "isb" ≠ ofString "k" by decide] using cursorLocal
    have codeResumed : resumed.code = originalRuntimeCode := metadata.1.trans code
    have scan := evaluate_versioned_hashes_scan_bounded resumed tx vh cursor txResumed vhResumed cursorResumed codeResumed
      (by change versionedHashesScanCost ≤ post.clock; omega)
    exact evaluate_sequence_straight_bounded resumed versionedHashesScan _ versionedHashesScanCost scan (by rfl)

#print axioms evaluate_versioned_hashes_typed_scan_bounded
end InitECandidate.Runtime
