import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Adding a conditional with an empty alternative adds no source clock cost. -/
theorem evaluate_conditional_skip_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (condition : ExpHOL 64) (body : ProgHOL 64) (cost : Nat)
    (bound : state.clock ≤ (evaluateHOLFiniteState state body).2.clock + cost ∧
      (evaluateHOLFiniteState state body).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state body).1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state (.ite condition body .skip)
    state.clock ≤ evaluated.2.clock + cost ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · simp [evaluateHOLFiniteState_skip]
    · exact bound
  · simp

#print axioms evaluate_conditional_skip_bounded
end InitECandidate.Runtime
