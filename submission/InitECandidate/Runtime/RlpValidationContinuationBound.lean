import InitECandidate.Runtime.RlpValidationListBound
import InitECandidate.Runtime.RlpHeaderSizedGeometry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Either valid header kind has a two-tick continuation budget, including
allocator traps and failed stores on the list branch. -/
theorem evaluate_rlpValidation_continuation_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (position header payload kind scratch frame : BitVec 64)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (headerLocal : state.locals.lookup (ofString "h") = some
      (.rStruct [.val (.word header),.val (.word payload),.val (.word kind)]))
    (flag : kind = 0 ∨ kind = 1)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpValidationHeaderContinuation
    state.clock ≤ evaluated.2.clock + 2 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  rcases flag with nonList | list
  · subst kind
    rw [evaluate_rlpValidation_non_list state position header payload positionLocal headerLocal]
    have clock := (rlpValidation_non_list_post state position header payload).2.1
    dsimp only at clock ⊢
    exact ⟨by omega,by omega,by simp⟩
  · subst kind
    exact evaluate_rlpValidation_list_continuation_bounded state position header payload scratch frame
      positionLocal headerLocal scratchGlobal frameGlobal code ticks

/-- The checked header predicate supplies the kind premise needed by the
uniform continuation budget at the actual returned result binding. -/
theorem evaluate_rlpValidation_sized_continuation_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (position length scratch frame : BitVec 64) (value : ValueHOL 64)
    (valid : RlpHeaderSizedProgress value length)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ≤ state.clock) :
    let entered := setVarHOLFinite (ofString "h") value state
    let evaluated := evaluateHOLFiniteState entered rlpValidationHeaderContinuation
    entered.clock ≤ evaluated.2.clock + 2 ∧ evaluated.2.clock ≤ entered.clock ∧ evaluated.1 ≠ some .timeOut := by
  obtain ⟨header,payload,kind,shape,_,_,_⟩ := valid.2
  subst value
  have fields := valid.fields header payload kind length
  apply evaluate_rlpValidation_continuation_bounded _ position header payload kind scratch frame
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "h" ≠ ofString "pos" by decide] using positionLocal
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · exact fields.1
  · exact scratchGlobal
  · exact frameGlobal
  · exact code
  · exact ticks

#print axioms evaluate_rlpValidation_continuation_bounded
#print axioms evaluate_rlpValidation_sized_continuation_bounded
end InitECandidate.Runtime
