import InitECandidate.Runtime.LocalAssignControl
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Normal local assignment exposes the actual evaluated value, rather than
only a state-update witness. -/
theorem evaluate_local_assign_normal_value {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (expression : ExpHOL 64)
    (run : evaluateHOLFiniteState state (.assign .local name expression) = (none,post)) :
    ∃ value, @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression = some value ∧
      post = setVarHOLFinite name value state := by
  rw [evaluateHOLFiniteState_assign] at run
  split at run
  · cases run
  · rename_i value evaluated
    split at run
    · exact ⟨value,evaluated,(Prod.mk.inj run).2.symm⟩
    · cases run

#print axioms evaluate_local_assign_normal_value
end InitECandidate.Runtime
