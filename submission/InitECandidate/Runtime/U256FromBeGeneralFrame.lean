import InitECandidate.Runtime.U256FromBeSource
import InitECandidate.Runtime.ReadOnlyGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem u256FromBe_initialized_readOnly : readOnlyMemory u256FromBeInitialized = true := by
  simp only [u256FromBeInitialized,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- General conversion retains all input slice entries and allocator globals,
including when it times out or fails a byte read. -/
theorem evaluate_u256FromBe_general_frame {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state u256FromBeInitialized).2.memory = state.memory ∧
      (evaluateHOLFiniteState state u256FromBeInitialized).2.globals = state.globals :=
  ⟨evaluate_readOnly_memory _ u256FromBe_initialized_readOnly state,
    evaluate_readOnly_globals _ u256FromBe_initialized_readOnly state⟩

#print axioms evaluate_u256FromBe_general_frame
end InitECandidate.Runtime
