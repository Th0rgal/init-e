import InitECandidate.Runtime.RlpValidationPushNormal
import InitECandidate.Runtime.RlpValidationStack
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal original list-push execution extends the linked stack through the
real scratch allocator, stores and result-local restoration. -/
theorem rlpValidation_allocated_stack {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (position stop payload after scratch frame : BitVec 64) (frames : List RlpValidationFrame)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (topLocal : state.locals.lookup (ofString "top") = some (.val (.word (rlpValidationStackTop frames))))
    (payloadLocal : state.locals.lookup (ofString "payload") = some (.val (.word payload)))
    (afterLocal : state.locals.lookup (ofString "after") = some (.val (.word after)))
    (stack : RlpValidationStack state.memory scratch.toNat frames)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ≤ state.clock)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < scratch.toNat → state.memaddrs address)
    (run : evaluateHOLFiniteState state rlpValidationListPush = (none,post)) :
    let record := scratchAllocationEnd scratch 24
    RlpValidationStack post.memory record.toNat ({record := record,resume := after,stop := stop} :: frames) := by
  have allocationRun := run
  rw [source_rlpValidation_list_push] at allocationRun
  obtain ⟨request,within,_⟩ := evaluate_scratch_alloc_decCall_normal state post (ofString "rec") (.const 24)
    rlpValidationPushStores scratch 24 frame (by rfl) scratchGlobal frameGlobal code ticks allocationRun
  have fits : 24 ≤ scratch.toNat := by
    have bound := BitVec.le_def.mp request
    rw [BitVec.toNat_sub_of_le orderedFrame] at bound
    change 24 ≤ scratch.toNat - frame.toNat at bound
    omega
  have nonzero : scratchAllocationEnd scratch 24 ≠ 0 := by
    intro zero
    have lower := BitVec.le_def.mp within
    rw [zero] at lower
    change frame.toNat ≤ 0 at lower
    omega
  let record := scratchAllocationEnd scratch 24
  obtain ⟨ready,_,_,memory,locals,_,addresses,_,_,_,declaration⟩ :=
    evaluate_scratch_alloc_call_and_declaration state (.const 24) scratch 24 frame (by rfl) code
      (by omega) scratchGlobal frameGlobal request within
  let entered := setVarHOLFinite (ofString "rec") (.val (.word record)) ready
  have localFrame : ∀ name, name ≠ ofString "rec" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
  have atRecord : entered.locals.lookup (ofString "rec") = some (.val (.word record)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have enteredStack : RlpValidationStack entered.memory scratch.toNat frames := by
    change RlpValidationStack ready.memory scratch.toNat frames
    rw [memory]
    exact stack
  have domain : ∀ field : Nat, field < 24 → entered.memaddrs (record + BitVec.ofNat 64 field) := by
    intro field inside
    have geometry := scratchAllocation_field_nat scratch 24 field fits inside
    change ready.memaddrs _
    rw [addresses]
    apply arena _ _ geometry.2
    have lower := BitVec.le_def.mp within
    rw [geometry.1]
    omega
  have stores := evaluate_rlpValidation_push_execution entered position stop (rlpValidationStackTop frames) record payload after
    ((localFrame _ (by decide)).trans positionLocal) ((localFrame _ (by decide)).trans stopLocal)
    ((localFrame _ (by decide)).trans topLocal) atRecord ((localFrame _ (by decide)).trans payloadLocal)
    ((localFrame _ (by decide)).trans afterLocal)
    (by simpa using domain 0 (by decide)) (domain 8 (by decide)) (domain 16 (by decide))
  have linked := enteredStack.push entered scratch after stop payload fits nonzero
  let output := rlpValidationPushPost entered record after stop (rlpValidationStackTop frames) payload
  have actual : evaluateHOLFiniteState state rlpValidationListPush =
      (none,{output with locals := HolFiniteMapExact.resVarEq output.locals (ofString "rec",state.locals.lookup (ofString "rec"))}) := by
    rw [source_rlpValidation_list_push,declaration]
    change (let result := evaluateHOLFiniteState entered rlpValidationPushStores; _) = _
    rw [stores]
  have equal := (Prod.mk.inj (actual.symm.trans run)).2
  rw [← equal]
  exact linked

#print axioms rlpValidation_allocated_stack
end InitECandidate.Runtime
