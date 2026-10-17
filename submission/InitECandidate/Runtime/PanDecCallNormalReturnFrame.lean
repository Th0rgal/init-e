import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A normally completed declaration-call must have executed its continuation
with caller locals restored, then restored the result variable's old binding.
The returned value additionally satisfies the checked callee property. -/
theorem evaluate_decCall_normal_return_frame {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (name function : MlS)
    (shape returnShape : ShapeHOL) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (property : ValueHOL 64 → Prop)
    (bodyProperty : ∀ value output, evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
      (some (.returned value),output) → property value)
    (bodyFrame : ∀ result output, evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
      (result,output) → output.memory = state.memory ∧ output.globals = state.globals)
    (run : evaluateHOLFiniteState state (.decCall name shape function arguments continuation) = (none,post)) :
    ∃ value ready output, property value ∧ ready.locals = state.locals ∧ ready.memory = state.memory ∧ ready.globals = state.globals ∧
      evaluateHOLFiniteState (setVarHOLFinite name value ready) continuation = (none,output) ∧
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
          · let ready := {(fixClockHOLFinite (callEntryStateHOLFinite state callee) (some (PanSemResultExact.returned value),bodyPost)).2 with locals := state.locals}
            change (let output := evaluateHOLFiniteState (setVarHOLFinite name value ready) continuation;
              (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name)})) = (none,post) at run
            cases tailRun : evaluateHOLFiniteState (setVarHOLFinite name value ready) continuation with
            | mk tailResult output =>
              rw [tailRun] at run
              have normal := (Prod.mk.inj run).1
              change tailResult = none at normal
              subst tailResult
              have frame := bodyFrame (some (.returned value)) bodyPost bodyRun
              exact ⟨value,ready,output,bodyProperty value bodyPost bodyRun,rfl,frame.1,frame.2,tailRun,(Prod.mk.inj run).2.symm⟩
          · cases run
        | error => cases run
        | timeOut => cases run
        | «break» => cases run
        | «continue» => cases run
        | exception exception value => cases run
        | finalFfi ffi => cases run

#print axioms evaluate_decCall_normal_return_frame
end InitECandidate.Runtime
