import InitECandidate.Runtime.RlpValidationHeaderCallState
import InitECandidate.Runtime.RlpValidationStackArena
import InitECandidate.Runtime.RlpValidationListSpace
import InitECandidate.Runtime.RlpValidationListGlobals
import InitECandidate.Runtime.RlpValidationListInvariant
import InitECandidate.Runtime.RlpValidationNonListInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal original header parsing preserves a linked stack at its actual
scratch global, with ordered frame/frontier globals and a fixed arena ceiling. -/
theorem rlpValidation_parse_state_invariant {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (position stop scratch frame : BitVec 64) (frames : List RlpValidationFrame)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (topLocal : state.locals.lookup (ofString "top") = some (.val (.word (rlpValidationStackTop frames))))
    (stack : RlpValidationStack state.memory scratch.toNat frames)
    (intervals : RlpValidationIntervals position stop frames)
    (inputBound : (stop - position).toNat + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (ticks : 14 ≤ state.clock)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < scratch.toNat → state.memaddrs address)
    (ceiling : Nat) (scratchBelow : scratch.toNat ≤ ceiling)
    (stackCeiling : RlpValidationStackCeiling ceiling frames)
    (run : evaluateHOLFiniteState state rlpValidationHeaderCall = (none,post)) :
    ∃ (newPosition newStop : BitVec 64) (frontier : BitVec 64) (newFrames : List RlpValidationFrame),
      post.locals.lookup (ofString "pos") = some (.val (.word newPosition)) ∧
      post.locals.lookup (ofString "end") = some (.val (.word newStop)) ∧
      post.locals.lookup (ofString "top") = some (.val (.word (rlpValidationStackTop newFrames))) ∧
      RlpValidationStack post.memory frontier.toNat newFrames ∧
      RlpValidationIntervals newPosition newStop newFrames ∧
      rlpValidationRank newPosition newStop newFrames < rlpValidationRank position stop frames ∧
      state.clock ≤ post.clock + 13 ∧
      RlpValidationStackCeiling ceiling newFrames ∧ frontier.toNat ≤ ceiling ∧
      post.globals.lookup (ofString "scratch_ptr") = some (.val (.word frontier)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧ frame ≤ frontier := by
  obtain ⟨value,ready,output,valid,locals,memory,globals,readyCode,domain,remaining,bound,tail,restored⟩ :=
    evaluate_rlpValidation_header_call_state state post position stop positionLocal stopLocal code (by omega) run
  obtain ⟨header,payload,kind,shape,_,_,_⟩ := valid.2
  subst value
  have fields := valid.fields header payload kind (stop - position)
  rcases fields.1 with nonList | list
  · subst kind
    have ordered : position.toNat ≤ stop.toNat := by
      cases intervals with
      | nil _ _ ordered => exact ordered
      | cons _ _ _ _ ordered _ _ => exact ordered
    have cursor := valid.cursor position stop header payload 0 ordered
    let entered := setVarHOLFinite (ofString "h")
      (.rStruct [.val (.word header),.val (.word payload),.val (.word 0)]) ready
    have localFrame : ∀ name, name ≠ ofString "h" → entered.locals.lookup name = state.locals.lookup name := by
      intro name different
      simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
    have atHeader : entered.locals.lookup (ofString "h") = some
        (.rStruct [.val (.word header),.val (.word payload),.val (.word 0)]) := by
      simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have actual := evaluate_rlpValidation_non_list entered position header payload
      ((localFrame _ (by decide)).trans positionLocal) atHeader
    have same := (Prod.mk.inj (tail.symm.trans actual)).2
    have result := rlpValidation_non_list_post entered position header payload
    have endFrame := rlpValidation_non_list_other_local entered position header payload (ofString "end") (by decide) (by decide) (by decide)
    have topFrame := rlpValidation_non_list_other_local entered position header payload (ofString "top") (by decide) (by decide) (by decide)
    refine ⟨position + header + payload,stop,scratch,frames,?_⟩
    rw [restored,same]
    refine ⟨?_,?_,?_,?_,intervals.reposition cursor.2,rlpValidation_rank_advance position _ stop frames cursor.1 cursor.2,?_⟩
    · rw [restore_other_local _ _ (ofString "pos") _ (by decide)]
      exact result.1
    · rw [restore_other_local _ _ (ofString "end") _ (by decide)]
      exact endFrame.trans ((localFrame _ (by decide)).trans stopLocal)
    · rw [restore_other_local _ _ (ofString "top") _ (by decide)]
      exact topFrame.trans ((localFrame _ (by decide)).trans topLocal)
    · change RlpValidationStack ready.memory scratch.toNat frames
      rw [memory]; exact stack
    · refine ⟨?_,stackCeiling,scratchBelow,?_,?_,orderedFrame⟩
      · have clock := result.2.1
        change (rlpValidationNonListPost entered position header payload).clock = ready.clock at clock
        change state.clock ≤ (rlpValidationNonListPost entered position header payload).clock + 13
        omega
      · change ready.globals.lookup _ = _
        rw [globals]; exact scratchGlobal
      · change ready.globals.lookup _ = _
        rw [globals]; exact frameGlobal
  · subst kind
    let entered := setVarHOLFinite (ofString "h")
      (.rStruct [.val (.word header),.val (.word payload),.val (.word 1)]) ready
    have localFrame : ∀ name, name ≠ ofString "h" → entered.locals.lookup name = state.locals.lookup name := by
      intro name different
      simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
    have atHeader : entered.locals.lookup (ofString "h") = some
        (.rStruct [.val (.word header),.val (.word payload),.val (.word 1)]) := by
      simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have enteredStack : RlpValidationStack entered.memory scratch.toNat frames := by
      change RlpValidationStack ready.memory scratch.toNat frames
      rw [memory]; exact stack
    have atScratch : entered.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) := by
      change ready.globals.lookup _ = _
      rw [globals]; exact scratchGlobal
    have atFrame : entered.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
      change ready.globals.lookup _ = _
      rw [globals]; exact frameGlobal
    have arenaEntered : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < scratch.toNat → entered.memaddrs address := by
      simpa only [entered,setVarHOLFinite,domain] using arena
    have result := rlpValidation_list_continuation_invariant entered output position stop header payload scratch frame frames
      ((localFrame _ (by decide)).trans positionLocal) ((localFrame _ (by decide)).trans stopLocal)
      ((localFrame _ (by decide)).trans topLocal) atHeader valid enteredStack intervals inputBound
      atScratch atFrame (readyCode.trans code) (by change 2 ≤ ready.clock; omega) orderedFrame framePositive arenaEntered tail
    have globalPost := rlpValidation_list_continuation_globals entered output position stop header payload scratch frame frames
      ((localFrame _ (by decide)).trans positionLocal) ((localFrame _ (by decide)).trans stopLocal)
      ((localFrame _ (by decide)).trans topLocal) atHeader atScratch atFrame (readyCode.trans code)
      (by change 2 ≤ ready.clock; omega) orderedFrame arenaEntered tail
    have space := rlpValidation_list_continuation_space entered output position header payload scratch frame
      ((localFrame _ (by decide)).trans positionLocal) atHeader atScratch atFrame (readyCode.trans code)
      (by change 2 ≤ ready.clock; omega) orderedFrame tail
    have ceilingPost := stackCeiling.push scratch (position + header + payload) stop space.1 scratchBelow
    have before := scratchAllocationEnd_before scratch 24 space.1
    change (scratchAllocationEnd scratch 24).toNat + 24 ≤ scratch.toNat at before
    refine ⟨position + header,position + header + payload,scratchAllocationEnd scratch 24,
      {record := scratchAllocationEnd scratch 24,resume := position + header + payload,stop := stop} :: frames,?_⟩
    dsimp only at result ⊢
    rw [restored]
    refine ⟨?_,?_,?_,result.2.2.2.1,result.2.2.2.2.1,result.2.2.2.2.2.1,?_⟩
    · rw [restore_other_local _ _ (ofString "pos") _ (by decide)]
      exact result.1
    · rw [restore_other_local _ _ (ofString "end") _ (by decide)]
      exact result.2.1
    · rw [restore_other_local _ _ (ofString "top") _ (by decide)]
      exact result.2.2.1
    · refine ⟨?_,ceilingPost,by omega,?_,?_,globalPost.2.1⟩
      · have clock := result.2.2.2.2.2.2
        change output.clock = ready.clock - 1 at clock
        change state.clock ≤ output.clock + 13
        omega
      · change output.globals.lookup _ = _
        rw [globalPost.1]
        simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      · change output.globals.lookup _ = _
        rw [globalPost.1]
        simpa [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
          show ofString "scratch_ptr" ≠ ofString "frame_mem_ptr" by decide] using atFrame


#print axioms rlpValidation_parse_state_invariant
end InitECandidate.Runtime
