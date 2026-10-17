import InitECandidate.Runtime.ScratchAllocationDecCallBound
import InitECandidate.Runtime.RlpValidationPushAllocation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual list push is bounded across successful allocation, either
allocator rejection, and failed continuation stores. No space premise is needed. -/
theorem evaluate_rlpValidation_list_push_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (scratch frame : BitVec 64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpValidationListPush
    state.clock ≤ evaluated.2.clock + 2 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  rw [source_rlpValidation_list_push]
  apply evaluate_scratch_alloc_decCall_straight_bounded state (.const 24) scratch 24 frame
    (ofString "rec") .one rlpValidationPushStores
  · rw [source_rlpValidation_push_stores,source_rlpValidation_push_updates]
    rfl
  · rfl
  · exact scratchGlobal
  · exact frameGlobal
  · exact code
  · exact ticks

#print axioms evaluate_rlpValidation_list_push_bounded
end InitECandidate.Runtime
