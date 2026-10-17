import InitECandidate.Runtime.RlpValidationPushGlobals
import InitECandidate.Runtime.RlpValidationListGlobalScope
import InitECandidate.Runtime.RlpValidationListContinuation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original list continuation updates only scratch_ptr and retains an
ordered frontier through its allocator and temporary scopes. -/
theorem rlpValidation_list_continuation_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (run : evaluateHOLFiniteState state rlpValidationHeaderContinuation = (none,post)) :
    post.globals = (setGlobalHOLFinite (ofString "scratch_ptr")
      (.val (.word (scratchAllocationEnd scratch 24))) state).globals ∧
      frame ≤ scratchAllocationEnd scratch 24 ∧ (scratchAllocationEnd scratch 24).toNat ≤ scratch.toNat := by
  obtain ⟨output,pushRun,globals⟩ := evaluate_rlpValidation_list_continuation_globals_scope state post position header payload
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
  have preserved := rlpValidation_list_push_globals entered output position stop (position + header)
    (position + header + payload) scratch frame frames
    ((localFrame _ (by decide) (by decide)).trans positionLocal) ((localFrame _ (by decide) (by decide)).trans stopLocal)
    ((localFrame _ (by decide) (by decide)).trans topLocal) atPayload atAfter scratchGlobal frameGlobal code ticks
    orderedFrame arena pushRun
  rw [globals]
  exact preserved

#print axioms rlpValidation_list_continuation_globals
end InitECandidate.Runtime
