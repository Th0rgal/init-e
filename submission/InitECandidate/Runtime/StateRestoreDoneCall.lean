import InitECandidate.Runtime.StateRestoreLoop
import InitECandidate.Runtime.OriginalStateRestoreCode
import InitECandidate.Runtime.PanSingleWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Empty undo work costs only the original call-entry clock, preserving
    the entire caller state except for that clock debit. -/
theorem evaluate_stateRestore_done_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (count snapshot : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
        some [.val (.word snapshot)])
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (done : count.toNat ≤ snapshot.toNat) :
    evaluateHOLFiniteState state (.call (some (none,none)) (ofString "state_restore") [argument]) =
      (none,{state with clock := state.clock - 1}) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    HolFiniteMapExact.empty.update (ofString "snap",.val (.word snapshot))
  let entry := callEntryStateHOLFinite state callee
  have snapshotLocal : entry.locals.lookup (ofString "snap") = some (.val (.word snapshot)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have body := evaluate_stateRestore_done entry count snapshot countGlobal snapshotLocal done
  have installed : state.code.lookup (ofString "state_restore") =
      some ([(ofString "snap",.one)],sourceFunctionBody Guest.guestFn_state_restore,.one) := by
    rw [code]; exact originalRuntimeCode_stateRestore_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "state_restore") (ofString "snap")
    (sourceFunctionBody Guest.guestFn_state_restore) snapshot installed
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "state_restore")
    [argument] [.val (.word snapshot)] (sourceFunctionBody Guest.guestFn_state_restore) callee .one (.val (.word 0))
    (emptyLocalsHOLFinite entry) arguments lookup clock body (by simp [shapeOfHOLExact,shapeEqHOL])
  exact call

#print axioms evaluate_stateRestore_done_call
end InitECandidate.Runtime
