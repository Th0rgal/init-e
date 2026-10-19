import InitECandidate.Runtime.ValidateHeadersFirstTailSource
import InitECandidate.Runtime.NormalLocalIncrementCalls
import InitECandidate.Runtime.DiscardCallSuccessLocals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original first-loop body increments i even across declaration scope
restoration; no decoder or Keccak runtime hypothesis is needed for this fact. -/
theorem validate_headers_first_body_increments :
    NormalLocalIncrement (ofString "i") validateHeadersFirstBody := by
  rw [source_validate_headers_first_decode]
  apply normalLocalIncrement_decCall _ _ _ _ _ _ (by decide)
  rw [source_validate_headers_first_tail]
  apply normalLocalIncrement_seq _ _ _ (by rfl)
  apply normalLocalIncrement_seq_normal_frame
  · intro F state post run
    have kept := evaluate_discard_call_success_locals state (ofString "keccak256") validateHeadersHashArguments
      (by change (evaluateHOLFiniteState state validateHeadersHashCall).1 = none; rw [run])
    change (evaluateHOLFiniteState state validateHeadersHashCall).2.locals = state.locals at kept
    rw [run] at kept
    rw [kept]
  · exact normalLocalIncrement_assign _

#print axioms validate_headers_first_body_increments
end InitECandidate.Runtime
