import InitECandidate.Runtime.AttemptWrapperBounds
import InitECandidate.Runtime.MainAttemptEntryPayloadReach
import InitECandidate.Runtime.MainNormalSuffixNoDomainBound
/-! The actual `mainAt 23` verify call, reduced to the normal output suffix. -/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The real `main` statement 23: the actual verify call, one-argument, result in `succ`, continuing
with the normal output serialization at `mainAt 24`. -/
theorem source_main_verify_call :
    mainAt 23 = (.decCall (ofString "succ") .one (ofString "verify_stateless_new_payload")
      [.var .local (ofString "si")] (mainAt 24) : ProgHOL 64) := by
  simp only [mainAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl
#print axioms source_main_verify_call
end InitECandidate.Runtime
