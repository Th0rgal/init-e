import InitECandidate.Runtime.VersionedHashesScanBound
import InitECandidate.Runtime.StraightLineNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem tx_is_blob_straight : straightLine (sourceFunctionBody Guest.guestFn_tx_is_blob) = true := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original type predicate costs no source ticks, including load failures. -/
theorem evaluate_tx_is_blob_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F) :
    let output := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_tx_is_blob)
    output.2.clock = state.clock ∧ output.1 ≠ some .timeOut := by
  exact ⟨clockPreserving_of_straightLine _ tx_is_blob_straight state,
    evaluate_straightLine_no_timeout _ tx_is_blob_straight state⟩

#print axioms tx_is_blob_straight
#print axioms evaluate_tx_is_blob_body_bounded
end InitECandidate.Runtime
