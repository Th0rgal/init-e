import InitECandidate.Runtime.NoDirectReturn
import InitECandidate.Runtime.RlpValidationPushAllocation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Actual validator steps cannot bypass the function return, including through
opaque header-parser or scratch-allocator callee returns. -/
theorem evaluate_rlpValidation_step_no_return {F : Type} (state : PanSemStateFiniteExact 64 F) (value : ValueHOL 64) :
    (evaluateHOLFiniteState state rlpValidationStep).1 ≠ some (.returned value) := by
  apply evaluate_noDirectReturn
  simp only [source_rlpValidation_step,source_rlpValidation_finished,source_rlpValidation_pop,
    source_rlpValidation_header_call,source_rlpValidation_header_continuation,source_rlpValidation_after_header,
    source_rlpValidation_list_push,source_rlpValidation_push_stores,source_rlpValidation_push_updates,noDirectReturn]
  rfl

#print axioms evaluate_rlpValidation_step_no_return
end InitECandidate.Runtime
