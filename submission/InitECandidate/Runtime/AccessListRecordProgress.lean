import InitECandidate.Runtime.AccessListSource
import InitECandidate.Runtime.NormalLocalIncrementCalls
import InitECandidate.Runtime.NormalLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual record stores complete with precisely one outer-index increment. -/
theorem accessRecordScope_increments : NormalLocalIncrement (ofString "i") accessRecordScope := by
  simp only [accessRecordScope,accessKeysLoopAndRecord,accessAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  apply normalLocalIncrement_dec _ _ _ _ _ (by decide)
  apply normalLocalIncrement_seq _ _ _ (by rfl)
  apply normalLocalIncrement_seq _ _ _ (by rfl)
  apply normalLocalIncrement_seq _ _ _ (by rfl)
  exact normalLocalIncrement_assign _

/-- The record-address scope and stores retain both outer-loop buffer bindings. -/
theorem access_record_scope_loop_locals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState state accessRecordScope = (none,post)) :
    post.locals.lookup (ofString "lst") = state.locals.lookup (ofString "lst") ∧
      post.locals.lookup (ofString "recs") = state.locals.lookup (ofString "recs") := by
  have listFrame : normalLocalFrameSyntax (ofString "lst") accessRecordScope = true := by
    simp only [accessRecordScope,accessKeysLoopAndRecord,accessAt,authorizationNext,sourceFunctionBody,
      InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
    rfl
  have recordsFrame : normalLocalFrameSyntax (ofString "recs") accessRecordScope = true := by
    simp only [accessRecordScope,accessKeysLoopAndRecord,accessAt,authorizationNext,sourceFunctionBody,
      InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
    rfl
  exact ⟨evaluate_normalLocalFrame _ _ listFrame state post run,
    evaluate_normalLocalFrame _ _ recordsFrame state post run⟩

#print axioms accessRecordScope_increments
#print axioms access_record_scope_loop_locals
end InitECandidate.Runtime
