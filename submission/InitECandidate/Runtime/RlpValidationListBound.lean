import InitECandidate.Runtime.RlpValidationListResultScope
import InitECandidate.Runtime.RlpValidationPushBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The full original list continuation costs at most two ticks across all
outcomes, including allocator rejection and failed stores. -/
theorem evaluate_rlpValidation_list_continuation_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (position header payload scratch frame : BitVec 64)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (headerLocal : state.locals.lookup (ofString "h") = some
      (.rStruct [.val (.word header),.val (.word payload),.val (.word 1)]))
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpValidationHeaderContinuation
    state.clock ≤ evaluated.2.clock + 2 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  cases run : evaluateHOLFiniteState state rlpValidationHeaderContinuation with
  | mk result post =>
    obtain ⟨output,pushRun,clock⟩ := evaluate_rlpValidation_list_continuation_result_scope state post position header payload
      positionLocal headerLocal result run
    have bounded := evaluate_rlpValidation_list_push_bounded (rlpValidationListEntry state position header payload)
      scratch frame scratchGlobal frameGlobal code ticks
    rw [pushRun] at bounded
    dsimp only at bounded ⊢
    have sameClock : (rlpValidationListEntry state position header payload).clock = state.clock := rfl
    exact ⟨by omega,by omega,bounded.2.2⟩

#print axioms evaluate_rlpValidation_list_continuation_bounded
end InitECandidate.Runtime
