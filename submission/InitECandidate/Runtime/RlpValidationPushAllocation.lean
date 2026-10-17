import InitECandidate.Runtime.RlpValidationPushExecution
import InitECandidate.Runtime.ScratchAllocationCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_rlpValidation_list_push : rlpValidationListPush =
    .decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 24] rlpValidationPushStores := by
  simp only [rlpValidationListPush,rlpValidationPushStores,rlpValidationAfterHeader,
    rlpValidationHeaderContinuation,rlpValidationHeaderCall,rlpValidationStep,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original list push allocates its 24-byte stack record, saves the
parent interval, enters the payload and restores the temporary record local. -/
theorem evaluate_rlpValidation_list_push {F : Type} (state : PanSemStateFiniteExact 64 F)
    (position stop top payload after scratch frame : BitVec 64)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (topLocal : state.locals.lookup (ofString "top") = some (.val (.word top)))
    (payloadLocal : state.locals.lookup (ofString "payload") = some (.val (.word payload)))
    (afterLocal : state.locals.lookup (ofString "after") = some (.val (.word after)))
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (request : (24 : BitVec 64) ≤ scratch - frame) (within : frame ≤ scratchAllocationEnd scratch 24)
    (domain0 : state.memaddrs (scratchAllocationEnd scratch 24))
    (domain8 : state.memaddrs (scratchAllocationEnd scratch 24 + 8))
    (domain16 : state.memaddrs (scratchAllocationEnd scratch 24 + 16)) :
    ∃ post, evaluateHOLFiniteState state rlpValidationListPush = (none,post) ∧
      post.clock = state.clock - 1 ∧
      post.locals.lookup (ofString "pos") = some (.val (.word payload)) ∧
      post.locals.lookup (ofString "end") = some (.val (.word after)) ∧
      post.locals.lookup (ofString "top") = some (.val (.word (scratchAllocationEnd scratch 24))) ∧
      post.memory (scratchAllocationEnd scratch 24) = .word after ∧
      post.memory (scratchAllocationEnd scratch 24 + 8) = .word stop ∧
      post.memory (scratchAllocationEnd scratch 24 + 16) = .word top := by
  let record := scratchAllocationEnd scratch 24
  obtain ⟨ready,_,clock,_,locals,_,addresses,_,_,_,declaration⟩ :=
    evaluate_scratch_alloc_call_and_declaration state (.const 24) scratch 24 frame (by rfl) code
      (by omega) scratchGlobal frameGlobal request within
  let entered := setVarHOLFinite (ofString "rec") (.val (.word record)) ready
  have localFrame : ∀ name, name ≠ ofString "rec" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
  have atRecord : entered.locals.lookup (ofString "rec") = some (.val (.word record)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have run := evaluate_rlpValidation_push_execution entered position stop top record payload after
    ((localFrame _ (by decide)).trans positionLocal) ((localFrame _ (by decide)).trans stopLocal)
    ((localFrame _ (by decide)).trans topLocal) atRecord ((localFrame _ (by decide)).trans payloadLocal)
    ((localFrame _ (by decide)).trans afterLocal)
    (by simpa only [entered,setVarHOLFinite,addresses,record] using domain0)
    (by simpa only [entered,setVarHOLFinite,addresses,record] using domain8)
    (by simpa only [entered,setVarHOLFinite,addresses,record] using domain16)
  have fields := rlpValidation_push_post entered record after stop top payload
  dsimp only at fields
  let output := rlpValidationPushPost entered record after stop top payload
  let final := {output with locals := HolFiniteMapExact.resVarEq output.locals (ofString "rec",state.locals.lookup (ofString "rec"))}
  refine ⟨final,?_,fields.2.2.2.2.2.2.1.trans clock,?_,?_,?_,fields.2.2.2.1,fields.2.2.2.2.1,fields.2.2.2.2.2.1⟩
  · rw [source_rlpValidation_list_push,declaration]
    change (let result := evaluateHOLFiniteState entered rlpValidationPushStores; _) = _
    rw [run]
  · change (HolFiniteMapExact.resVarEq output.locals _).lookup (ofString "pos") = _
    rw [restore_other_local _ _ (ofString "pos") _ (by decide)]
    exact fields.1
  · change (HolFiniteMapExact.resVarEq output.locals _).lookup (ofString "end") = _
    rw [restore_other_local _ _ (ofString "end") _ (by decide)]
    exact fields.2.1
  · change (HolFiniteMapExact.resVarEq output.locals _).lookup (ofString "top") = _
    rw [restore_other_local _ _ (ofString "top") _ (by decide)]
    exact fields.2.2.1

#print axioms evaluate_rlpValidation_list_push
end InitECandidate.Runtime
