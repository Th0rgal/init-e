import InitECandidate.Runtime.HeapReleaseCall
import InitECandidate.Runtime.PanDiscardCallNormalResult
import InitECandidate.Runtime.ReadOnlyGlobals
import InitECandidate.Runtime.AllocationFramedGlobals
import InitECandidate.Runtime.NoDirectReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned release body proves that the real heap assignment succeeded.
No premise about the old heap value is needed for this returned-run fact. -/
theorem heapRelease_body_returned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (mark : BitVec 64) (value : ValueHOL 64)
    (marker : state.locals.lookup (ofString "m") = some (.val (.word mark)))
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_heap_release) =
      (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word mark)) := by
  rw [source_heapRelease_body] at run
  obtain ⟨middle,assigned,returned⟩ := seq_returned_of_nonreturning_first
    (fun returnedValue => evaluate_noDirectReturn _ (by rfl) state returnedValue) run
  have heap : middle.globals.lookup (ofString "heap_ptr") = some (.val (.word mark)) := by
    rw [evaluateHOLFiniteState_assign] at assigned
    simp only [evalHOLExact,marker] at assigned
    split at assigned
    · cases assigned
      simp [setKvarHOLFinite,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · cases assigned
  have globals := evaluate_readOnly_globals (.return (.const 0)) (by rfl) middle
  rw [returned] at globals
  rw [globals]
  exact heap

/-- A normally completed actual release call sets the saved frontier, even
when no old-heap typing premise was available before the call. -/
theorem heapRelease_call_normal {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (mark : BitVec 64) (code : state.code = originalRuntimeCode)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [argument] = some [.val (.word mark)])
    (run : evaluateHOLFiniteState state
      (.call (some (none,none)) (ofString "heap_release") [argument]) = (none,post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word mark)) := by
  have installed : state.code.lookup (ofString "heap_release") =
      some ([(ofString "m",.one)],sourceFunctionBody Guest.guestFn_heap_release,.one) := by
    rw [code]
    exact originalRuntimeCode_heap_release_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "heap_release") (ofString "m")
    (sourceFunctionBody Guest.guestFn_heap_release) mark installed
  obtain ⟨value,bodyPost,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post
    (ofString "heap_release") .one [argument] [.val (.word mark)]
    (sourceFunctionBody Guest.guestFn_heap_release)
    (HolFiniteMapExact.empty.update (ofString "m",.val (.word mark))) args lookup run
  rw [postEq]
  exact heapRelease_body_returned _ bodyPost mark value
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) bodyRun

#print axioms heapRelease_body_returned
#print axioms heapRelease_call_normal
end InitECandidate.Runtime
