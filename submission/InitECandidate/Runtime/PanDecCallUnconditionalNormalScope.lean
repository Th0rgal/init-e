import InitECandidate.Runtime.PanDecCallNormalReturnProperty
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Normal declaration calls expose their actual continuation and restored caller
locals, without argument-evaluation or installed-code premises. -/
theorem evaluate_decCall_unconditional_normal_scope {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64))
    (continuation : ProgHOL 64)
    (run : evaluateHOLFiniteState state (.decCall name shape function arguments continuation) = (none,post)) :
    ∃ value ready output, ready.locals = state.locals ∧
      evaluateHOLFiniteState (setVarHOLFinite name value ready) continuation = (none,output) ∧
      post = {output with locals := HolFiniteMapExact.resVarEq output.locals (name,state.locals.lookup name)} := by
  cases args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
  | none => rw [evaluateHOLFiniteState_decCall_total,args] at run; cases run
  | some values =>
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => rw [evaluateHOLFiniteState_decCall_total,args] at run; dsimp only at run; rw [lookup] at run; cases run
    | some installed =>
      obtain ⟨body,callee,returnShape⟩ := installed
      obtain ⟨value,ready,output,_,locals,tail,restored⟩ := evaluate_decCall_normal_return_property state post name function
        shape returnShape arguments values body continuation callee args lookup (fun _ => True)
        (by intro _ _ _; trivial) run
      exact ⟨value,ready,output,locals,tail,restored⟩

#print axioms evaluate_decCall_unconditional_normal_scope
end InitECandidate.Runtime
