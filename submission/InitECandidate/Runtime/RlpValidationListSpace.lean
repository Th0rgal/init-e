import InitECandidate.Runtime.RlpValidationListStack
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal completion of a list continuation certifies that its real scratch
allocation fit, including the allocator's rounded lower-bound check. -/
theorem rlpValidation_list_continuation_space {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (position header payload scratch frame : BitVec 64)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (headerLocal : state.locals.lookup (ofString "h") = some
      (.rStruct [.val (.word header),.val (.word payload),.val (.word 1)]))
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ≤ state.clock) (orderedFrame : frame ≤ scratch)
    (run : evaluateHOLFiniteState state rlpValidationHeaderContinuation = (none,post)) :
    24 ≤ scratch.toNat ∧ frame ≤ scratchAllocationEnd scratch 24 := by
  obtain ⟨output,pushRun,_,_,_⟩ := evaluate_rlpValidation_list_continuation_normal state post position header payload
    positionLocal headerLocal run
  rw [source_rlpValidation_list_push] at pushRun
  obtain ⟨request,within,_⟩ := evaluate_scratch_alloc_decCall_normal
    (rlpValidationListEntry state position header payload) output (ofString "rec") (.const 24)
    rlpValidationPushStores scratch 24 frame (by rfl) scratchGlobal frameGlobal code ticks pushRun
  have bound := BitVec.le_def.mp request
  rw [BitVec.toNat_sub_of_le orderedFrame] at bound
  change 24 ≤ scratch.toNat - frame.toNat at bound
  exact ⟨by omega,within⟩

#print axioms rlpValidation_list_continuation_space
end InitECandidate.Runtime
