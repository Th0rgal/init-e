import InitECandidate.Runtime.RlpValidationParseInvariant
import InitECandidate.Runtime.RlpValidationPopInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A normally completed original validator step either clears the loop flag,
or preserves the stack and interval invariants with strictly smaller rank.
Every progressing step costs at most thirteen source ticks. -/
theorem rlpValidation_step_invariant {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (flag : BitVec 64)
    (flagLocal : state.locals.lookup (ofString "go") = some (.val (.word flag)))
    (readableStack : ∀ saved ∈ frames, state.memaddrs saved.record ∧
      state.memaddrs (saved.record + 8) ∧ state.memaddrs (saved.record + 16))
    (run : evaluateHOLFiniteState state rlpValidationStep = (none,post)) :
    (post.locals.lookup (ofString "go") = some (.val (.word 0)) ∧ post.clock = state.clock) ∨
    ∃ (newPosition newStop : BitVec 64) (frontier : Nat) (newFrames : List RlpValidationFrame),
      post.locals.lookup (ofString "pos") = some (.val (.word newPosition)) ∧
      post.locals.lookup (ofString "end") = some (.val (.word newStop)) ∧
      post.locals.lookup (ofString "top") = some (.val (.word (rlpValidationStackTop newFrames))) ∧
      RlpValidationStack post.memory frontier newFrames ∧
      RlpValidationIntervals newPosition newStop newFrames ∧
      rlpValidationRank newPosition newStop newFrames < rlpValidationRank position stop frames ∧
      state.clock ≤ post.clock + 13 := by
  by_cases finished : position = stop
  · subst position
    cases frames with
    | nil =>
      have actual := evaluate_rlpValidation_finish_empty state stop flag positionLocal stopLocal topLocal flagLocal
      have same := (Prod.mk.inj (run.symm.trans actual)).2
      left
      rw [same]
      constructor
      · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      · rfl
    | cons saved rest =>
      have readable := readableStack saved (by simp)
      obtain ⟨output,actual,atPosition,atStop,atTop,validStack,validIntervals,decreases,clock,_⟩ :=
        evaluate_rlpValidation_pop_invariant state stop scratch.toNat saved rest positionLocal stopLocal topLocal
          stack intervals readable.1 readable.2.1 readable.2.2
      have same := (Prod.mk.inj (run.symm.trans actual)).2
      right
      rw [same]
      exact ⟨saved.resume,saved.stop,scratch.toNat,rest,atPosition,atStop,atTop,validStack,validIntervals,decreases,by omega⟩
  · right
    have headerRun := (evaluate_rlpValidation_step_header state position stop positionLocal stopLocal finished).symm.trans run
    exact rlpValidation_parse_invariant state post position stop scratch frame frames positionLocal stopLocal topLocal
      stack intervals inputBound scratchGlobal frameGlobal code ticks orderedFrame framePositive arena headerRun

#print axioms rlpValidation_step_invariant
end InitECandidate.Runtime
