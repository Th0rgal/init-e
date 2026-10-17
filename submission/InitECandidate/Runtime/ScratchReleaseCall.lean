import InitECandidate.Runtime.OriginalScratchReleaseCode
import InitECandidate.Runtime.ScratchCleanupSource
import InitECandidate.Runtime.PanSingleWordLookup
import InitECandidate.Runtime.PanDecCallReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original release call restores scratch_ptr, preserves caller locals
and memory, and spends precisely its one call-entry tick. -/
theorem evaluate_scratchRelease_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (scratch mark : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
      some [.val (.word mark)])
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (code : state.code = originalRuntimeCode) (ticks : state.clock ≠ 0) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "scratch_release") [argument]) = (none,post) ∧
      post.clock = state.clock - 1 ∧ post.memory = state.memory ∧ post.locals = state.locals ∧
      post.globals = (setGlobalHOLFinite (ofString "scratch_ptr") (.val (.word mark)) state).globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "m",.val (.word mark))
  let entry := callEntryStateHOLFinite state callee
  have markLocal : entry.locals.lookup (ofString "m") = some (.val (.word mark)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have body := evaluate_scratch_release_body entry scratch mark scratchGlobal markLocal
  have installed : state.code.lookup (ofString "scratch_release") =
      some ([(ofString "m",.one)],sourceFunctionBody Guest.guestFn_scratch_release,.one) := by
    rw [code]; exact originalRuntimeCode_scratchRelease_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "scratch_release") (ofString "m")
    (sourceFunctionBody Guest.guestFn_scratch_release) mark installed
  have shape : shapeEqHOL (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) .one = true := by
    simp [shapeOfHOLExact,shapeEqHOL]
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "scratch_release") [argument]
    [.val (.word mark)] (sourceFunctionBody Guest.guestFn_scratch_release) callee .one (.val (.word 0))
    (emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "scratch_ptr") (.val (.word mark)) entry)) args lookup ticks body shape
  exact ⟨_,call,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms evaluate_scratchRelease_call
end InitECandidate.Runtime
