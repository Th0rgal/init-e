import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Normal completion of a one-word declaration proves its returned value
is a word via the evaluator's checked shape, and restores caller locals
before the continuation. No callee correctness assumption is needed. -/
theorem evaluate_decCall_one_normal_word_frame {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (name function : MlS)
    (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,.one))
    (bodyFrame : ∀ result output, evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
      (result,output) → output.memory = state.memory ∧ output.globals = state.globals)
    (run : evaluateHOLFiniteState state (.decCall name .one function arguments continuation) = (none,post)) :
    ∃ (word : BitVec 64) (ready output : PanSemStateFiniteExact 64 F), ready.locals = state.locals ∧ ready.memory = state.memory ∧ ready.globals = state.globals ∧
      evaluateHOLFiniteState (setVarHOLFinite name (.val (.word word)) ready) continuation = (none,output) ∧
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
              (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name)})) = (none,post) at run
            cases tailRun : evaluateHOLFiniteState (setVarHOLFinite name value ready) continuation with
            | mk tailResult output =>
              rw [tailRun] at run
              have normal := (Prod.mk.inj run).1
              change tailResult = none at normal
              subst tailResult
              have frame := bodyFrame _ _ bodyRun
              refine ⟨word,ready,output,rfl,?_,?_,tailRun,(Prod.mk.inj run).2.symm⟩
              · change (fixClockHOLFinite (callEntryStateHOLFinite state callee) (some (PanSemResultExact.returned value),bodyPost)).2.memory = _
                unfold fixClockHOLFinite
                split <;> exact frame.1
              · change (fixClockHOLFinite (callEntryStateHOLFinite state callee) (some (PanSemResultExact.returned value),bodyPost)).2.globals = _
                unfold fixClockHOLFinite
                split <;> exact frame.2
          · cases run
        | error => cases run
        | timeOut => cases run
        | «break» => cases run
        | «continue» => cases run
        | exception exception value => cases run
        | finalFfi ffi => cases run

#print axioms evaluate_decCall_one_normal_word_frame
end InitECandidate.Runtime
