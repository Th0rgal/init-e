import InitECandidate.Runtime.RlpValidationStepInvariant
import InitECandidate.Runtime.RlpValidationParseCeiling
import InitECandidate.Runtime.RlpValidationStackArena
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original normal validator step preserves a fixed upper scratch ceiling
through parsing and popping, or terminates by clearing its loop flag. -/
theorem rlpValidation_step_ceiling_invariant {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (ceiling : Nat) (scratchBelow : scratch.toNat ≤ ceiling)
    (stackCeiling : RlpValidationStackCeiling ceiling frames)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (flag : BitVec 64)
    (flagLocal : state.locals.lookup (ofString "go") = some (.val (.word flag)))
    (run : evaluateHOLFiniteState state rlpValidationStep = (none,post)) :
    (post.locals.lookup (ofString "go") = some (.val (.word 0)) ∧ post.clock = state.clock) ∨
    ∃ (newPosition newStop : BitVec 64) (frontier : Nat) (newFrames : List RlpValidationFrame),
      post.locals.lookup (ofString "pos") = some (.val (.word newPosition)) ∧
      post.locals.lookup (ofString "end") = some (.val (.word newStop)) ∧
      post.locals.lookup (ofString "top") = some (.val (.word (rlpValidationStackTop newFrames))) ∧
      RlpValidationStack post.memory frontier newFrames ∧
      RlpValidationIntervals newPosition newStop newFrames ∧
      rlpValidationRank newPosition newStop newFrames < rlpValidationRank position stop frames ∧
      state.clock ≤ post.clock + 13 ∧
      RlpValidationStackCeiling ceiling newFrames ∧ frontier ≤ ceiling := by
  have readable := stack.readable state stackCeiling (by
    intro address lower upper
    apply arena address _ upper
    have ordered := BitVec.le_def.mp orderedFrame
    omega)
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
      have domains := readable saved (by simp)
      obtain ⟨output,actual,atPosition,atStop,atTop,validStack,validIntervals,decreases,clock,_⟩ :=
        evaluate_rlpValidation_pop_invariant state stop scratch.toNat saved rest positionLocal stopLocal topLocal
          stack intervals domains.1 domains.2.1 domains.2.2
      have same := (Prod.mk.inj (run.symm.trans actual)).2
      right
      rw [same]
      exact ⟨saved.resume,saved.stop,scratch.toNat,rest,atPosition,atStop,atTop,validStack,validIntervals,
        decreases,by omega,stackCeiling.tail,scratchBelow⟩
  · right
    have headerRun := (evaluate_rlpValidation_step_header state position stop positionLocal stopLocal finished).symm.trans run
    exact rlpValidation_parse_ceiling_invariant state post position stop scratch frame frames
      positionLocal stopLocal topLocal stack intervals inputBound scratchGlobal frameGlobal code ticks
      orderedFrame framePositive (by
        intro address lower upper
        exact arena address lower (by omega)) ceiling scratchBelow stackCeiling headerRun

#print axioms rlpValidation_step_ceiling_invariant
end InitECandidate.Runtime
