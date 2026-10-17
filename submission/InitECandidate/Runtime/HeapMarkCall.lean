import InitECandidate.Runtime.OriginalHeapControlCode
import InitECandidate.Runtime.PanNoArgsLookup
import InitECandidate.Runtime.PanDecCallReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_heapMark_body : sourceFunctionBody Guest.guestFn_heap_mark =
    .return (.var .global (ofString "heap_ptr")) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original heap marker reads the frontier and consumes only call entry;
its declaration makes that exact frontier available to the continuation. -/
theorem evaluate_heapMark_call_and_declaration {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (ticks : state.clock ≠ 0) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "heap_mark") []) = (none,post) ∧
      post.clock = state.clock - 1 ∧ post.memory = state.memory ∧ post.globals = state.globals ∧ post.locals = state.locals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ name continuation, evaluateHOLFiniteState state (.decCall name .one (ofString "heap_mark") [] continuation) =
        (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word pointer)) post) continuation;
          (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name)}))) := by
  let entry := callEntryStateHOLFinite state HolFiniteMapExact.empty
  have body : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_heap_mark) =
      (some (.returned (.val (.word pointer))),emptyLocalsHOLFinite entry) := by
    rw [source_heapMark_body]
    simp [evaluateHOLFiniteState_return,evalHOLExact,show entry.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)) from heap,shapeOfHOLExact]
  have installed : state.code.lookup (ofString "heap_mark") = some ([],sourceFunctionBody Guest.guestFn_heap_mark,.one) := by
    rw [code]
    exact originalRuntimeCode_heap_mark_lookup
  have lookup := pan_no_args_lookup state.code.lookup (ofString "heap_mark") (sourceFunctionBody Guest.guestFn_heap_mark) installed
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [] = some [] := rfl
  have shape : shapeEqHOL (shapeOfHOLExact (.val (.word pointer))) .one = true := by simp [shapeOfHOLExact,shapeEqHOL]
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "heap_mark") [] []
    (sourceFunctionBody Guest.guestFn_heap_mark) HolFiniteMapExact.empty .one (.val (.word pointer)) (emptyLocalsHOLFinite entry) args lookup ticks body shape
  let post := {emptyLocalsHOLFinite entry with locals := state.locals}
  refine ⟨post,call,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  intro name continuation
  have declaration := evaluate_decCall_return_caller_locals state (emptyLocalsHOLFinite entry) name (ofString "heap_mark") .one .one [] []
    (sourceFunctionBody Guest.guestFn_heap_mark) continuation HolFiniteMapExact.empty (.val (.word pointer)) args lookup ticks body
    (Nat.le_refl _) shape shape
  exact declaration

#print axioms source_heapMark_body
#print axioms evaluate_heapMark_call_and_declaration
end InitECandidate.Runtime
