import InitECandidate.Runtime.RlpValidationPushNormal
import InitECandidate.Runtime.RlpValidationPushAllocation
import InitECandidate.Runtime.RlpValidationPushLowerFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_rlpValidation_list_push_lower_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (fits : 24 ≤ scratch.toNat)
    (domain0 : state.memaddrs (scratchAllocationEnd scratch 24))
    (domain8 : state.memaddrs (scratchAllocationEnd scratch 24 + 8))
    (domain16 : state.memaddrs (scratchAllocationEnd scratch 24 + 16)) :
    ∃ post, evaluateHOLFiniteState state rlpValidationListPush = (none,post) ∧
      ∀ watched : BitVec 64, watched.toNat < frame.toNat → post.memory watched = state.memory watched := by
  let record := scratchAllocationEnd scratch 24
  obtain ⟨ready,_,clock,memory,locals,_,addresses,_,_,_,declaration⟩ :=
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
  let output := rlpValidationPushPost entered record after stop top payload
  let final := {output with locals := HolFiniteMapExact.resVarEq output.locals (ofString "rec",state.locals.lookup (ofString "rec"))}
  refine ⟨final,?_,?_⟩
  · rw [source_rlpValidation_list_push,declaration]
    change (let result := evaluateHOLFiniteState entered rlpValidationPushStores; _) = _
    rw [run]
  · intro watched below
    have frameRead := rlpValidation_scratch_push_memory_below_frame entered scratch frame after stop top payload watched fits
      (BitVec.le_def.mp within) below
    change output.memory watched = state.memory watched
    exact frameRead.trans (congrFun memory watched)

theorem rlpValidation_list_push_normal_lower_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (position stop top payload after scratch frame : BitVec 64)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (topLocal : state.locals.lookup (ofString "top") = some (.val (.word top)))
    (payloadLocal : state.locals.lookup (ofString "payload") = some (.val (.word payload)))
    (afterLocal : state.locals.lookup (ofString "after") = some (.val (.word after)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ≤ state.clock)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (orderedFrame : frame ≤ scratch)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < scratch.toNat → state.memaddrs address)
    (run : evaluateHOLFiniteState state rlpValidationListPush = (none,post)) :
    ∀ watched : BitVec 64, watched.toNat < frame.toNat → post.memory watched = state.memory watched := by
  have allocationRun := run
  rw [source_rlpValidation_list_push] at allocationRun
  obtain ⟨request,within,_⟩ := evaluate_scratch_alloc_decCall_normal state post (ofString "rec") (.const 24)
    rlpValidationPushStores scratch 24 frame (by rfl) scratchGlobal frameGlobal code ticks allocationRun
  have fits : 24 ≤ scratch.toNat := by
    have bound := BitVec.le_def.mp request
    rw [BitVec.toNat_sub_of_le orderedFrame] at bound
    change 24 ≤ scratch.toNat - frame.toNat at bound
    omega
  have domain (offset : Nat) (inside : offset < 24) : state.memaddrs (scratchAllocationEnd scratch 24 + BitVec.ofNat 64 offset) := by
    have fields := scratchAllocation_field_nat scratch 24 offset fits inside
    apply arena
    · have lower := BitVec.le_def.mp within
      rw [fields.1]
      omega
    · exact fields.2
  obtain ⟨expected,actual,frameRead⟩ := evaluate_rlpValidation_list_push_lower_frame state position stop top payload after scratch frame
    positionLocal stopLocal topLocal payloadLocal afterLocal code (by omega) scratchGlobal frameGlobal request within fits
    (by simpa only [show BitVec.ofNat 64 0 = 0#64 from rfl,BitVec.add_zero] using domain 0 (by decide))
    (domain 8 (by decide)) (domain 16 (by decide))
  have equal := (Prod.mk.inj (actual.symm.trans run)).2
  subst post
  exact frameRead

#print axioms rlpValidation_list_push_normal_lower_frame
#print axioms evaluate_rlpValidation_list_push_lower_frame
end InitECandidate.Runtime
