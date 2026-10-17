import InitECandidate.Runtime.RlpValidationStepInvariant
import InitECandidate.Runtime.RlpValidationStackArena
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A fixed scratch arena supplies both allocation readability and saved-record
readability for the actual normal validator step. -/
theorem rlpValidation_step_arena_invariant {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
      state.clock ≤ post.clock + 13 := by
  have readable := stack.readable state stackCeiling (by
    intro address lower upper
    apply arena address _ upper
    have ordered := BitVec.le_def.mp orderedFrame
    omega)
  exact rlpValidation_step_invariant state post position stop scratch frame frames
    positionLocal stopLocal topLocal stack intervals inputBound scratchGlobal frameGlobal code ticks
    orderedFrame framePositive (by
      intro address lower upper
      exact arena address lower (by omega)) flag flagLocal readable run

#print axioms rlpValidation_step_arena_invariant
end InitECandidate.Runtime
