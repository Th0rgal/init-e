import InitECandidate.Runtime.HeapReleaseReturned
import InitECandidate.Runtime.ReadOnlyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original release helper changes a global but never writes memory,
even if assignment validation fails. -/
theorem heapRelease_body_memory {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_heap_release)).2.memory = state.memory := by
  rw [source_heapRelease_body,evaluateHOLFiniteState_seq_line780]
  have frame : (evaluateHOLFiniteState state
      (.assign .global (ofString "heap_ptr") (.var .local (ofString "m")))).2.memory = state.memory := by
    rw [evaluateHOLFiniteState_assign]
    split
    · rfl
    · split <;> rfl
  cases assigned : evaluateHOLFiniteState state (.assign .global (ofString "heap_ptr") (.var .local (ofString "m"))) with
  | mk result next =>
    rw [assigned] at frame
    cases result with
    | some stopped => exact frame
    | none => exact (evaluate_readOnly_memory (.return (.const 0)) rfl next).trans frame

theorem heapRelease_call_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (mark : BitVec 64) (code : state.code = originalRuntimeCode)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [argument] =
      some [.val (.word mark)])
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "heap_release") [argument]) = (none,post)) :
    post.memory = state.memory := by
  have installed : state.code.lookup (ofString "heap_release") =
      some ([(ofString "m",.one)],sourceFunctionBody Guest.guestFn_heap_release,.one) := by
    rw [code]; exact originalRuntimeCode_heap_release_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "heap_release") (ofString "m")
    (sourceFunctionBody Guest.guestFn_heap_release) mark installed
  obtain ⟨value,output,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "heap_release")
    .one [argument] _ _ _ args lookup run
  have memory := heapRelease_body_memory
    (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "m",.val (.word mark))))
  rw [bodyRun] at memory
  rw [postEq]
  exact memory

#print axioms heapRelease_body_memory
#print axioms heapRelease_call_normal_memory
end InitECandidate.Runtime
