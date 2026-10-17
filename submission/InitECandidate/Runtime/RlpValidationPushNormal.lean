import InitECandidate.Runtime.RlpValidationPushArena
import InitECandidate.Runtime.ScratchAllocationCallResult
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A normally completed original list push supplies its own allocator-space
conditions; ordered scratch arena coverage suffices for the exact postconditions. -/
theorem rlpValidation_list_push_normal_post {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
      post.clock = state.clock - 1 ∧
      post.locals.lookup (ofString "pos") = some (.val (.word payload)) ∧
      post.locals.lookup (ofString "end") = some (.val (.word after)) ∧
      post.locals.lookup (ofString "top") = some (.val (.word (scratchAllocationEnd scratch 24))) ∧
      post.memory (scratchAllocationEnd scratch 24) = .word after ∧
      post.memory (scratchAllocationEnd scratch 24 + 8) = .word stop ∧
      post.memory (scratchAllocationEnd scratch 24 + 16) = .word top := by
  have allocationRun := run
  rw [source_rlpValidation_list_push] at allocationRun
  obtain ⟨request,within,_⟩ := evaluate_scratch_alloc_decCall_normal state post (ofString "rec") (.const 24)
    rlpValidationPushStores scratch 24 frame (by rfl) scratchGlobal frameGlobal code ticks allocationRun
  have fits : 24 ≤ scratch.toNat := by
    have bound := BitVec.le_def.mp request
    rw [BitVec.toNat_sub_of_le orderedFrame] at bound
    change 24 ≤ scratch.toNat - frame.toNat at bound
    omega
  obtain ⟨expected,actual,clock,positionPost,endPost,topPost,field0,field8,field16⟩ :=
    evaluate_rlpValidation_list_push_arena state position stop top payload after scratch frame
      positionLocal stopLocal topLocal payloadLocal afterLocal code (by omega) scratchGlobal frameGlobal
      request within fits arena
  have equal := (Prod.mk.inj (actual.symm.trans run)).2
  subst post
  exact ⟨clock,positionPost,endPost,topPost,field0,field8,field16⟩

#print axioms rlpValidation_list_push_normal_post
end InitECandidate.Runtime
