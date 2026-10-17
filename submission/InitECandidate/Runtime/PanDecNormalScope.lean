import InitECandidate.Runtime.PanDecCallNormalScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Normal declaration completion identifies a successful initializer and body,
with exactly the declared local restored around the body's final state. -/
theorem evaluate_dec_normal_scope {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64) (body : ProgHOL 64)
    (run : evaluateHOLFiniteState state (.dec name shape initializer body) = (none,post)) :
    ∃ value output,
      @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address)) initializer = some value ∧
      evaluateHOLFiniteState (setVarHOLFinite name value state) body = (none,output) ∧
      post = {output with locals := HolFiniteMapExact.resVarEq output.locals (name,state.locals.lookup name)} := by
  rw [evaluateHOLFiniteState_dec_total] at run
  dsimp only at run
  split at run
  · cases run
  · rename_i value initialized
    split at run
    · cases bodyRun : evaluateHOLFiniteState (setVarHOLFinite name value state) body with
      | mk result output =>
        rw [bodyRun] at run
        have normal := (Prod.mk.inj run).1
        change result = none at normal
        subst result
        exact ⟨value,output,initialized,bodyRun,(Prod.mk.inj run).2.symm⟩
    · cases run

#print axioms evaluate_dec_normal_scope
end InitECandidate.Runtime
