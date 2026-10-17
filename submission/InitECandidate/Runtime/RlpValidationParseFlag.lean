import InitECandidate.Runtime.RlpValidationHeaderCallState
import InitECandidate.Runtime.RlpValidationListFlag
import InitECandidate.Runtime.RlpValidationNonListInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A normally completed original header parsing call preserves the loop flag
for both item kinds, including the header-result temporary restoration. -/
theorem rlpValidation_parse_flag {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    post.locals.lookup (ofString "go") = state.locals.lookup (ofString "go") := by
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
  have preserved : output.locals.lookup (ofString "go") = entered.locals.lookup (ofString "go") := by
    rcases fields.1 with nonList | list
    · subst kind
      have actual := evaluate_rlpValidation_non_list entered position header payload atPosition atHeader
      have same := (Prod.mk.inj (tail.symm.trans actual)).2
      rw [same]
      exact rlpValidation_non_list_other_local entered position header payload (ofString "go") (by decide) (by decide) (by decide)
    · subst kind
      have atScratch : entered.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) := by
        change ready.globals.lookup _ = _
        rw [globals]; exact scratchGlobal
      have atFrame : entered.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
        change ready.globals.lookup _ = _
        rw [globals]; exact frameGlobal
      have arenaEntered : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < scratch.toNat → entered.memaddrs address := by
        simpa only [entered,setVarHOLFinite,domain] using arena
      exact rlpValidation_list_continuation_flag entered output position stop header payload scratch frame frames
        atPosition ((localFrame _ (by decide)).trans stopLocal) ((localFrame _ (by decide)).trans topLocal)
        atHeader atScratch atFrame (readyCode.trans code) (by change 2 ≤ ready.clock; omega) orderedFrame arenaEntered tail
  rw [restored,restore_other_local _ _ (ofString "go") _ (by decide)]
  exact preserved.trans (localFrame _ (by decide))

#print axioms rlpValidation_parse_flag
end InitECandidate.Runtime
