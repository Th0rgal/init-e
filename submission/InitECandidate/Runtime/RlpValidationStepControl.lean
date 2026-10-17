import InitECandidate.Runtime.NoLoopControlStores
import InitECandidate.Runtime.RlpValidationPushAllocation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The actual validator step never emits break or continue, including from
failed stores and opaque callees in either header parsing or scratch allocation. -/
theorem evaluate_rlpValidation_step_no_loop_control {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state rlpValidationStep).1 ≠ some .break ∧
      (evaluateHOLFiniteState state rlpValidationStep).1 ≠ some .continue := by
  apply evaluate_noLoopControlStores
  simp only [source_rlpValidation_step,source_rlpValidation_finished,source_rlpValidation_pop,
    source_rlpValidation_header_call,source_rlpValidation_header_continuation,source_rlpValidation_after_header,
    source_rlpValidation_list_push,source_rlpValidation_push_stores,source_rlpValidation_push_updates,noLoopControlStores]
  rfl

#print axioms evaluate_rlpValidation_step_no_loop_control
end InitECandidate.Runtime
