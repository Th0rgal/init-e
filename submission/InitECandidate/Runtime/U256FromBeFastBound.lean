import InitECandidate.Runtime.U256FromBeGeneralBound
import InitECandidate.Runtime.RuntimeClockBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The original aligned conversion executes at most four byte-swap calls.
Failed loads and argument/shape failures are included. -/
theorem u256FromBe_fast_body_bounded : RuntimeClockBound u256FromBeFastBody 4 := by
  simp only [u256FromBeFastBody,u256FromBeFastGuard,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  apply runtimeClockBound_dec
  apply runtimeClockBound_bswap64 _ _ _ _ 3
  apply runtimeClockBound_prefix _ _ 3 (by rfl)
  apply runtimeClockBound_bswap64 _ _ _ _ 2
  apply runtimeClockBound_prefix _ _ 2 (by rfl)
  apply runtimeClockBound_bswap64 _ _ _ _ 1
  apply runtimeClockBound_prefix _ _ 1 (by rfl)
  apply runtimeClockBound_bswap64 _ _ _ _ 0
  exact runtimeClockBound_straight _ (by rfl)

#print axioms u256FromBe_fast_body_bounded
end InitECandidate.Runtime
