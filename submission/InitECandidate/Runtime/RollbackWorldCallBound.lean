import InitECandidate.Runtime.RollbackWorldFunctionBound
import InitECandidate.Runtime.RollbackWorldRead
import InitECandidate.Runtime.OriginalStateRestoreCode
import InitECandidate.Runtime.PanSingleWordLookup
import InitECandidate.Runtime.DiscardCallNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual original state_restore call inherits the all-plan bound; the
world's snapshot binding is installed only for the function's local scope. -/
theorem rollback_world_call_bounded_no_timeout {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64)) (journal snapshot count : BitVec 64)
    (world : RollbackWorld widths tables journal snapshot count
      (setVarHOLFinite (ofString "snap") (.val (.word snapshot)) state))
    (separated : RollbackPhysicalSeparated widths tables state)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (argument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] = some [.val (.word snapshot)])
    (code : state.code = originalRuntimeCode) (budget : 2 ^ 92 + 1 ≤ state.clock) :
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "state_restore") [argument])).1 ≠ some .timeOut ∧
    state.clock ≤ (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "state_restore") [argument])).2.clock + (2 ^ 92 + 1) ∧
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "state_restore") [argument])).2.clock ≤ state.clock := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "snap",.val (.word snapshot))
  let entry := callEntryStateHOLFinite state callee
  have snap : entry.locals.lookup (ofString "snap") =
      (setVarHOLFinite (ofString "snap") (.val (.word snapshot)) state).locals.lookup (ofString "snap") := by
    simp [entry,callEntryStateHOLFinite,callee,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryWorld := world.after_read (after := entry) rfl rfl rfl rfl rfl snap
  have entrySeparated := separated.after_read (after := entry) rfl rfl rfl rfl rfl
  obtain ⟨result,post,run,cost,remaining,noTimeout⟩ := entryWorld.function_bounded_no_timeout entrySeparated heapDomain
    (by change 2 ^ 92 ≤ state.clock - 1; omega)
  have installed : state.code.lookup (ofString "state_restore") =
      some ([(ofString "snap",.one)],sourceFunctionBody Guest.guestFn_state_restore,.one) := by
    rw [code]; exact originalRuntimeCode_stateRestore_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "state_restore") (ofString "snap")
    (sourceFunctionBody Guest.guestFn_state_restore) snapshot installed
  have timeout := evaluate_discard_call_body_no_timeout state post (ofString "state_restore") [argument] [.val (.word snapshot)]
    (sourceFunctionBody Guest.guestFn_state_restore) callee .one result arguments lookup (by omega) run noTimeout
  have clock := evaluate_discard_call_body_clock state post (ofString "state_restore") [argument] [.val (.word snapshot)]
    (sourceFunctionBody Guest.guestFn_state_restore) callee .one result arguments lookup (by omega) run
  refine ⟨timeout,?_,?_⟩
  · rw [clock]
    change state.clock - 1 ≤ post.clock + 2 ^ 92 at cost
    omega
  · rw [clock]
    change post.clock ≤ state.clock - 1 at remaining
    omega

#print axioms rollback_world_call_bounded_no_timeout
end InitECandidate.Runtime
