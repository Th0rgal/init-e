import InitECandidate.Runtime.ScratchMarkCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- Exact original marker declaration: only its call-entry clock tick and its
scoped mark binding differ before the actual continuation. -/
theorem evaluate_scratch_mark_declaration_exact {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (code : state.code=originalRuntimeCode)
    (heap : state.globals.lookup (ofString "scratch_ptr")=some (.val (.word pointer)))
    (ticks : state.clock≠0) (continuation : ProgHOL 64) :
    evaluateHOLFiniteState state (.decCall (ofString "mark") .one (ofString "scratch_mark") [] continuation)=
      (let output := evaluateHOLFiniteState
        (setVarHOLFinite (ofString "mark") (.val (.word pointer)) {state with clock:=state.clock-1}) continuation;
       (output.1,{output.2 with locals:=HolFiniteMapExact.resVarEq output.2.locals (ofString "mark",state.locals.lookup (ofString "mark"))})) := by
  let entry := callEntryStateHOLFinite state HolFiniteMapExact.empty
  have body : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_scratch_mark) =
      (some (.returned (.val (.word pointer))),emptyLocalsHOLFinite entry) := by
    rw [source_scratchMark_body]
    simp [evaluateHOLFiniteState_return,evalHOLExact,show entry.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)) from heap,shapeOfHOLExact]
  have installed : state.code.lookup (ofString "scratch_mark") = some ([],sourceFunctionBody Guest.guestFn_scratch_mark,.one) := by
    rw [code]
    exact originalRuntimeCode_scratchMark_lookup
  have lookup := pan_no_args_lookup state.code.lookup (ofString "scratch_mark") (sourceFunctionBody Guest.guestFn_scratch_mark) installed
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [] = some [] := rfl
  have shape : shapeEqHOL (shapeOfHOLExact (.val (.word pointer))) .one = true := by simp [shapeOfHOLExact,shapeEqHOL]
  have declaration := evaluate_decCall_return_caller_locals state (emptyLocalsHOLFinite entry) (ofString "mark")
    (ofString "scratch_mark") .one .one [] [] (sourceFunctionBody Guest.guestFn_scratch_mark) continuation HolFiniteMapExact.empty
    (.val (.word pointer)) args lookup ticks body (Nat.le_refl _) shape shape
  simpa only [entry,callEntryStateHOLFinite,emptyLocalsHOLFinite] using declaration
#print axioms evaluate_scratch_mark_declaration_exact
end InitECandidate.Runtime
