import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A normal declaration-call exposes its actual callee and continuation,
including the callee clock retained after clock clamping and local restoration. -/
theorem evaluate_decCall_normal_global_clock_scope {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (name function : MlS)
    (shape returnShape : ShapeHOL) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (run : evaluateHOLFiniteState state (.decCall name shape function arguments continuation) = (none,post)) :
    ∃ value bodyPost ready output,
      evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (some (.returned value),bodyPost) ∧
      ready.locals = state.locals ∧ ready.globals = bodyPost.globals ∧ ready.clock = bodyPost.clock ∧
      ready.memaddrs = bodyPost.memaddrs ∧ ready.be = bodyPost.be ∧ ready.code = bodyPost.code ∧
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
              have remaining := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
              rw [bodyRun] at remaining
              refine ⟨value,bodyPost,ready,output,rfl,rfl,?_,?_,?_,?_,?_,tailRun,(Prod.mk.inj run).2.symm⟩
              all_goals simp [ready,fixClockHOLFinite,Nat.not_lt.mpr remaining]
          · cases run
        | error => cases run
        | timeOut => cases run
        | «break» => cases run
        | «continue» => cases run
        | exception exception value => cases run
        | finalFfi ffi => cases run


#print axioms evaluate_decCall_normal_global_clock_scope
end InitECandidate.Runtime
