import InitECandidate.Runtime.RlpValidationHeaderCallState
import InitECandidate.Runtime.RlpValidationListGlobals
import InitECandidate.Runtime.RlpValidationNonListInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal original header parsing leaves a typed scratch pointer between the
frame pointer and its old value, and preserves frame_mem_ptr. -/
theorem rlpValidation_parse_named_global {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (watched : MlS) (different : ofString "scratch_ptr" ≠ watched)
    (position stop scratch frame : BitVec 64) (frames : List RlpValidationFrame)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (topLocal : state.locals.lookup (ofString "top") = some (.val (.word (rlpValidationStackTop frames))))
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (ticks : 14 ≤ state.clock)
    (orderedFrame : frame ≤ scratch)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < scratch.toNat → state.memaddrs address)
    (run : evaluateHOLFiniteState state rlpValidationHeaderCall = (none,post)) :
    post.globals.lookup watched = state.globals.lookup watched := by
  obtain ⟨value,ready,output,valid,locals,memory,globals,readyCode,domain,remaining,bound,tail,restored⟩ :=
    evaluate_rlpValidation_header_call_state state post position stop positionLocal stopLocal code (by omega) run
  obtain ⟨header,payload,kind,shape,_,_,_⟩ := valid.2
  subst value
  have fields := valid.fields header payload kind (stop - position)
  let entered := setVarHOLFinite (ofString "h")
    (.rStruct [.val (.word header),.val (.word payload),.val (.word kind)]) ready
  have localFrame : ∀ name, name ≠ ofString "h" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
  have atHeader : entered.locals.lookup (ofString "h") = some
      (.rStruct [.val (.word header),.val (.word payload),.val (.word kind)]) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atPosition := (localFrame (ofString "pos") (by decide)).trans positionLocal
  rw [restored]
  change output.globals.lookup watched = state.globals.lookup watched
  rcases fields.1 with nonList | list
  · subst kind
    have actual := evaluate_rlpValidation_non_list entered position header payload atPosition atHeader
    have same := (Prod.mk.inj (tail.symm.trans actual)).2
    rw [same]
    have unchanged := (rlpValidation_non_list_post entered position header payload).2.2.2
    change (rlpValidationNonListPost entered position header payload).globals = ready.globals at unchanged
    rw [unchanged,globals]
  · subst kind
    have atScratch : entered.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) := by
      change ready.globals.lookup _ = _
      rw [globals]; exact scratchGlobal
    have atFrame : entered.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
      change ready.globals.lookup _ = _
      rw [globals]; exact frameGlobal
    have arenaEntered : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < scratch.toNat → entered.memaddrs address := by
      simpa only [entered,setVarHOLFinite,domain] using arena
    have result := rlpValidation_list_continuation_globals entered output position stop header payload scratch frame frames
      atPosition ((localFrame _ (by decide)).trans stopLocal) ((localFrame _ (by decide)).trans topLocal)
      atHeader atScratch atFrame (readyCode.trans code) (by change 2 ≤ ready.clock; omega) orderedFrame arenaEntered tail
    rw [result.1]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,entered,setVarHOLFinite,globals]

#print axioms rlpValidation_parse_named_global
end InitECandidate.Runtime
