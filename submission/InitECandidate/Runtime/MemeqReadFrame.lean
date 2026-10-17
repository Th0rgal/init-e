import InitECandidate.Runtime.ReadOnlyGlobals
import InitECandidate.Runtime.MemeqBody64Bound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Checked on the authoritative original memeq body, including both word
loops, both byte loops and all fixed-length fast paths. -/
theorem memeq_readOnlyMemory : readOnlyMemory (sourceFunctionBody Guest.guestFn_memeq) = true := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Original memeq preserves memory and globals for all lengths and fuel,
including invalid pointers and timed-out comparisons. -/
theorem evaluate_memeq_read_frame {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_memeq)).2.memory = state.memory ∧
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_memeq)).2.globals = state.globals :=
  ⟨evaluate_readOnly_memory _ memeq_readOnlyMemory state,evaluate_readOnly_globals _ memeq_readOnlyMemory state⟩

#print axioms memeq_readOnlyMemory
#print axioms evaluate_memeq_read_frame
end InitECandidate.Runtime
