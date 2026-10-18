import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
import InitECandidate.Runtime.PanDecCallCheckedNormalIntro
import InitECandidate.Runtime.NoDirectReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Split a returned declaration continuation after a prefix that cannot return.
Reconstructing the standalone declaration permits reuse of its normal-run contracts. -/
theorem evaluate_decCall_returned_append_scope {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (name function : MlS)
    (shape returnShape : ShapeHOL) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body first tail : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (finalValue : ValueHOL 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (nonzero : state.clock ≠ 0) (noReturnSyntax : noDirectReturn first = true)
    (run : evaluateHOLFiniteState state (.decCall name shape function arguments (.seq first tail)) = (some (.returned finalValue),post)) :
    ∃ value bodyPost middle output,
      evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (some (.returned value),bodyPost) ∧
      (shapeEqHOL (shapeOfHOLExact value) shape = true ∧ shapeEqHOL (shapeOfHOLExact value) returnShape = true) ∧
      evaluateHOLFiniteState (setVarHOLFinite name value {bodyPost with locals := state.locals}) first = (none,middle) ∧
      evaluateHOLFiniteState middle tail = (some (.returned finalValue),output) ∧
      evaluateHOLFiniteState state (.decCall name shape function arguments first) =
        (none,{middle with locals := HolFiniteMapExact.resVarEq middle.locals (name,state.locals.lookup name)}) ∧
      post = {output with locals := HolFiniteMapExact.resVarEq output.locals (name,state.locals.lookup name)} := by
  obtain ⟨value,bodyPost,output,bodyRun,checked,continuation,restored⟩ :=
    evaluate_decCall_checked_returned_exact_scope state post name function shape returnShape arguments values body (.seq first tail)
      callee finalValue args lookup run
  have noReturn := evaluate_noDirectReturn first noReturnSyntax
    (setVarHOLFinite name value {bodyPost with locals := state.locals}) finalValue
  rw [evaluateHOLFiniteState_seq_line780] at continuation
  cases firstRun : evaluateHOLFiniteState (setVarHOLFinite name value {bodyPost with locals := state.locals}) first with
  | mk result middle =>
    rw [firstRun] at continuation noReturn
    cases result with
    | some result => exact False.elim (noReturn (Prod.mk.inj continuation).1)
    | none =>
      exact ⟨value,bodyPost,middle,output,bodyRun,checked,firstRun,continuation,
        evaluate_decCall_checked_normal_intro state bodyPost middle name function shape returnShape arguments values body first callee value
          args lookup nonzero bodyRun checked firstRun,restored⟩

#print axioms evaluate_decCall_returned_append_scope
end InitECandidate.Runtime
