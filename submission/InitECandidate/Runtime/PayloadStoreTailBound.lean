import InitECandidate.Runtime.AuthorizationsTailSource
import InitECandidate.Runtime.StraightLineNoTimeout
import InitECandidate.Runtime.NamedGlobalFrame
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

def payloadAt (n : Nat) : ProgHOL 64 :=
  (authorizationNext^[n]) (sourceFunctionBody Guest.guestFn_decode_payload)

/-- After the fixed-list count call, the original payload decoder has only
header stores and its return remaining. -/
theorem payload_store_tail_straight : straightLine (payloadAt 20) = true := by
  simp only [payloadAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem payload_store_tail_no_global_assignment (key : MlS) :
    avoidsGlobalAssignment key (payloadAt 20) = true := by
  simp only [payloadAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- This suffix consumes no source clock and preserves allocator globals,
including header-store failures. -/
theorem evaluate_payload_store_tail_bounded {F : Type} (state : PanSemStateFiniteExact 64 F) :
    let evaluated := evaluateHOLFiniteState state (payloadAt 20)
    evaluated.2.clock = state.clock ∧ evaluated.1 ≠ some .timeOut ∧
      ∀ key, evaluated.2.globals.lookup key = state.globals.lookup key := by
  exact ⟨clockPreserving_of_straightLine _ payload_store_tail_straight state,
    evaluate_straightLine_no_timeout _ payload_store_tail_straight state,
    fun key => evaluate_avoidsGlobalAssignment key _ (payload_store_tail_no_global_assignment key) state⟩

#print axioms payload_store_tail_straight
#print axioms evaluate_payload_store_tail_bounded
end InitECandidate.Runtime
