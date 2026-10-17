import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A returned one-word declaration proves its callee value
is a word via the evaluator's checked shape, and restores caller locals
before the returned continuation. No callee correctness assumption is needed. -/
theorem evaluate_decCall_one_returned_word {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (name function : MlS)
    (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,.one))
    (finalValue : ValueHOL 64)
    (run : evaluateHOLFiniteState state (.decCall name .one function arguments continuation) = (some (.returned finalValue),post)) :
    ∃ (word : BitVec 64) (ready output : PanSemStateFiniteExact 64 F), ready.locals = state.locals ∧
      evaluateHOLFiniteState (setVarHOLFinite name (.val (.word word)) ready) continuation = (some (.returned finalValue),output) ∧
      post = {output with locals := HolFiniteMapExact.resVarEq output.locals (name,state.locals.lookup name)} := by
  rw [evaluateHOLFiniteState_decCall_total,args] at run
  dsimp only at run
  rw [lookup] at run
  dsimp only at run
  split at run
  · cases run
  · cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
    | mk result bodyPost =>
      rw [bodyRun] at run
      dsimp only at run
      cases result with
      | none => cases run
      | some result =>
        cases result with
        | returned value =>
          simp only at run
          split at run
          · rename_i goodShape
            have wordShape : ∃ word : BitVec 64, value = .val (.word word) := by
              cases value with
              | val atom => cases atom with | word word => exact ⟨word,rfl⟩
              | rStruct fields => simp [shapeOfHOLExact,shapeEqHOL] at goodShape
              | nStruct name fields => simp [shapeOfHOLExact,shapeEqHOL] at goodShape
            obtain ⟨word,rfl⟩ := wordShape
            let value : ValueHOL 64 := .val (.word word)
            let ready := {(fixClockHOLFinite (callEntryStateHOLFinite state callee) (some (PanSemResultExact.returned value),bodyPost)).2 with locals := state.locals}
            change (let output := evaluateHOLFiniteState (setVarHOLFinite name value ready) continuation;
              (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name)})) = (some (.returned finalValue),post) at run
            cases tailRun : evaluateHOLFiniteState (setVarHOLFinite name value ready) continuation with
            | mk tailResult output =>
              rw [tailRun] at run
              have normal := (Prod.mk.inj run).1
              change tailResult = some (.returned finalValue) at normal
              subst tailResult
              exact ⟨word,ready,output,rfl,tailRun,(Prod.mk.inj run).2.symm⟩
          · cases run
        | error => cases run
        | timeOut => cases run
        | «break» => cases run
        | «continue» => cases run
        | exception exception value => cases run
        | finalFfi ffi => cases run

#print axioms evaluate_decCall_one_returned_word
end InitECandidate.Runtime
