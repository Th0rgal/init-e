import InitECandidate.Runtime.AuthorizationsStepSource
import InitECandidate.Runtime.NoLoopControlStores
import InitECandidate.Runtime.NoDirectReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The actual iteration cannot escape by break, continue or a returned
callee value; only normal completion or a genuine terminal result remains. -/
theorem evaluate_authorization_step_control {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state authorizationStep).1 ≠ some .break ∧
      (evaluateHOLFiniteState state authorizationStep).1 ≠ some .continue ∧
      (∀ value, (evaluateHOLFiniteState state authorizationStep).1 ≠ some (.returned value)) := by
  have noControl : noLoopControlStores authorizationStep = true := by
    simp only [authorizationStep,authorizationAt,authorizationNext,sourceFunctionBody,
      InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
    rfl
  have noReturn : noDirectReturn authorizationStep = true := by
    simp only [authorizationStep,authorizationAt,authorizationNext,sourceFunctionBody,
      InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
    rfl
  have control := evaluate_noLoopControlStores authorizationStep noControl state
  exact ⟨control.1,control.2,fun value => evaluate_noDirectReturn authorizationStep noReturn state value⟩

#print axioms evaluate_authorization_step_control
end InitECandidate.Runtime
