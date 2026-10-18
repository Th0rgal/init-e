import InitECandidate.Runtime.RlpValidationPushLocalFrame
import InitECandidate.Runtime.RlpValidationPushFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpValidation_list_push_memory_above_scratch {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (position stop payload after scratch frame : BitVec 64) (frames : List RlpValidationFrame)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (topLocal : state.locals.lookup (ofString "top") = some (.val (.word (rlpValidationStackTop frames))))
    (payloadLocal : state.locals.lookup (ofString "payload") = some (.val (.word payload)))
    (afterLocal : state.locals.lookup (ofString "after") = some (.val (.word after)))
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ≤ state.clock)
    (orderedFrame : frame ≤ scratch)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < scratch.toNat → state.memaddrs address)
    (run : evaluateHOLFiniteState state rlpValidationListPush = (none,post)) (address : BitVec 64) (above : scratch.toNat ≤ address.toNat) :
    post.memory address = state.memory address := by
  have allocationRun := run
  rw [source_rlpValidation_list_push] at allocationRun
  obtain ⟨request,within,_⟩ := evaluate_scratch_alloc_decCall_normal state post (ofString "rec") (.const 24)
    rlpValidationPushStores scratch 24 frame (by rfl) scratchGlobal frameGlobal code ticks allocationRun
  have fits : 24 ≤ scratch.toNat := by
    have bound := BitVec.le_def.mp request
    rw [BitVec.toNat_sub_of_le orderedFrame] at bound
    change 24 ≤ scratch.toNat - frame.toNat at bound
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
  let output := rlpValidationPushPost entered record after stop (rlpValidationStackTop frames) payload
  have actual : evaluateHOLFiniteState state rlpValidationListPush =
      (none,{output with locals := HolFiniteMapExact.resVarEq output.locals (ofString "rec",state.locals.lookup (ofString "rec"))}) := by
    rw [source_rlpValidation_list_push,declaration]
    change (let result := evaluateHOLFiniteState entered rlpValidationPushStores; _) = _
    rw [stores]
  have equal := (Prod.mk.inj (actual.symm.trans run)).2
  rw [← equal]
  have preserved := rlpValidation_push_memory_above entered scratch after stop (rlpValidationStackTop frames) payload address fits above
  exact preserved.trans (congrFun memory address)

#print axioms rlpValidation_list_push_memory_above_scratch
end InitECandidate.Runtime
