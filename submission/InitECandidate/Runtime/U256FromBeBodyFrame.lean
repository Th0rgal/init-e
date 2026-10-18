import InitECandidate.Runtime.RuntimeFrame
import InitECandidate.Runtime.U256FromBeGeneralBound
import InitECandidate.Runtime.U256FromBeGeneralFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem u256FromBe_fast_body_frame : RuntimeFrame u256FromBeFastBody := by
  simp only [u256FromBeFastBody,u256FromBeFastGuard,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  apply runtimeFrame_dec
  apply runtimeFrame_bswap64
  apply runtimeFrame_seq _ _ (runtimeFrame_readOnly _ (by rfl))
  apply runtimeFrame_bswap64
  apply runtimeFrame_seq _ _ (runtimeFrame_readOnly _ (by rfl))
  apply runtimeFrame_bswap64
  apply runtimeFrame_seq _ _ (runtimeFrame_readOnly _ (by rfl))
  apply runtimeFrame_bswap64
  exact runtimeFrame_readOnly _ (by rfl)

/-- The complete original converter preserves all memory and globals,
including either conversion path, failed input reads and timeout. -/
theorem u256FromBe_body_frame : RuntimeFrame (sourceFunctionBody Guest.guestFn_u256_from_be) := by
  rw [source_u256FromBe_body]
  apply runtimeFrame_seq
  · rw [source_u256FromBe_fast_guard]
    exact runtimeFrame_ite _ _ _ u256FromBe_fast_body_frame (runtimeFrame_readOnly _ (by rfl))
  · exact runtimeFrame_readOnly _ u256FromBe_initialized_readOnly

#print axioms u256FromBe_body_frame
end InitECandidate.Runtime
