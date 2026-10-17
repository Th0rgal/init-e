import InitECandidate.Runtime.NoLoopControl
import InitECandidate.Runtime.TrieWalkStepBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The exact original loop body contains neither escaping loop control nor
handlers that can introduce it. Callee controls are checked at call boundaries. -/
theorem trieWalkStep_noLoopControl : noLoopControl trieWalkStep = true := by
  simp only [trieWalkStep,trieWalkLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evaluate_trieWalk_step_no_loop_control {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state trieWalkStep).1 ≠ some .break ∧
    (evaluateHOLFiniteState state trieWalkStep).1 ≠ some .continue :=
  evaluate_noLoopControl _ trieWalkStep_noLoopControl state

#print axioms trieWalkStep_noLoopControl
#print axioms evaluate_trieWalk_step_no_loop_control
end InitECandidate.Runtime
