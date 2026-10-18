import InitECandidate.Runtime.NormalLocalFrame
import InitECandidate.Runtime.AuthorizationsStepSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem authorizationStep_list_local_frame : normalLocalFrameSyntax (ofString "lst") authorizationStep = true := by
  simp only [authorizationStep,authorizationAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem authorizationStep_records_local_frame : normalLocalFrameSyntax (ofString "recs") authorizationStep = true := by
  simp only [authorizationStep,authorizationAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Every successful authorization iteration retains the outer list/count
and records-buffer bindings, independently of the implementations it called. -/
theorem evaluate_authorization_step_loop_locals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState state authorizationStep = (none,post)) :
    post.locals.lookup (ofString "lst") = state.locals.lookup (ofString "lst") ∧
      post.locals.lookup (ofString "recs") = state.locals.lookup (ofString "recs") :=
  ⟨evaluate_normalLocalFrame _ _ authorizationStep_list_local_frame state post run,
    evaluate_normalLocalFrame _ _ authorizationStep_records_local_frame state post run⟩

#print axioms evaluate_authorization_step_loop_locals
end InitECandidate.Runtime
