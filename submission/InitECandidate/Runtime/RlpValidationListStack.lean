import InitECandidate.Runtime.RlpValidationAllocatedStack
import InitECandidate.Runtime.RlpValidationListContinuation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A normally completed original list continuation extends the linked stack
through its computed cursor declarations and scratch allocation. -/
theorem rlpValidation_list_continuation_stack {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (position stop header payload scratch frame : BitVec 64) (frames : List RlpValidationFrame)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (topLocal : state.locals.lookup (ofString "top") = some (.val (.word (rlpValidationStackTop frames))))
    (headerLocal : state.locals.lookup (ofString "h") = some
      (.rStruct [.val (.word header),.val (.word payload),.val (.word 1)]))
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ≤ state.clock) (orderedFrame : frame ≤ scratch)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < scratch.toNat → state.memaddrs address)
    (stack : RlpValidationStack state.memory scratch.toNat frames)
    (framePositive : 0 < frame.toNat)
    (run : evaluateHOLFiniteState state rlpValidationHeaderContinuation = (none,post)) :
    let record := scratchAllocationEnd scratch 24
    RlpValidationStack post.memory record.toNat
      ({record := record,resume := position + header + payload,stop := stop} :: frames) := by
  obtain ⟨output,pushRun,_,memory,_⟩ := evaluate_rlpValidation_list_continuation_normal state post position header payload
    positionLocal headerLocal run
  let entered := rlpValidationListEntry state position header payload
  have localFrame : ∀ name, name ≠ ofString "payload" → name ≠ ofString "after" → entered.locals.lookup name = state.locals.lookup name := by
    intro name differentPayload differentAfter
    simp [entered,rlpValidationListEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      Ne.symm differentPayload,Ne.symm differentAfter]
  have atPayload : entered.locals.lookup (ofString "payload") = some (.val (.word (position + header))) := by
    simp [entered,rlpValidationListEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "after" ≠ ofString "payload" by decide]
  have atAfter : entered.locals.lookup (ofString "after") = some (.val (.word (position + header + payload))) := by
    simp [entered,rlpValidationListEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have linked := rlpValidation_allocated_stack entered output position stop (position + header)
    (position + header + payload) scratch frame frames
    ((localFrame _ (by decide) (by decide)).trans positionLocal) ((localFrame _ (by decide) (by decide)).trans stopLocal)
    ((localFrame _ (by decide) (by decide)).trans topLocal) atPayload atAfter stack scratchGlobal frameGlobal code ticks
    orderedFrame framePositive arena pushRun
  rw [memory]
  exact linked

#print axioms rlpValidation_list_continuation_stack
end InitECandidate.Runtime
