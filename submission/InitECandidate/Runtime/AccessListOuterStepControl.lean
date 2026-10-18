import InitECandidate.Runtime.AccessListSource
import InitECandidate.Runtime.NoLoopControlWhile
import InitECandidate.Runtime.NoDirectReturnWhile
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The actual iteration cannot escape by break, continue or a returned
callee value; only normal completion or a genuine terminal result remains. -/
theorem evaluate_access_outer_step_control {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state accessStep).1 ≠ some .break ∧
      (evaluateHOLFiniteState state accessStep).1 ≠ some .continue ∧
      (∀ value, (evaluateHOLFiniteState state accessStep).1 ≠ some (.returned value)) := by
  have noControl : noLoopControlWhile accessStep = true := by
    simp only [accessStep,accessAt,authorizationNext,sourceFunctionBody,
      InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
    rfl
  have noReturn : noDirectReturnWhile accessStep = true := by
    simp only [accessStep,accessAt,authorizationNext,sourceFunctionBody,
      InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
    rfl
  have control := evaluate_noLoopControlWhile accessStep noControl state
  exact ⟨control.1,control.2,fun value => evaluate_noDirectReturnWhile accessStep noReturn state value⟩

#print axioms evaluate_access_outer_step_control
end InitECandidate.Runtime
