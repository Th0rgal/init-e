import InitECandidate.Runtime.SourceClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Local assignment either updates that local only or fails without changing
the state. Expression and shape failures are included. -/
theorem evaluate_local_assign_control {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (value : ExpHOL 64) :
    (∃ assigned, evaluateHOLFiniteState state (.assign .local name value) =
      (none,setVarHOLFinite name assigned state)) ∨
    evaluateHOLFiniteState state (.assign .local name value) = (some .error,state) := by
  rw [evaluateHOLFiniteState_assign]
  split
  · exact Or.inr rfl
  · split
    · exact Or.inl ⟨_,rfl⟩
    · exact Or.inr rfl

#print axioms evaluate_local_assign_control
end InitECandidate.Runtime
