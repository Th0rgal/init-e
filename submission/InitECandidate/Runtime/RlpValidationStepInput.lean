import InitECandidate.Runtime.RlpValidationStepArena
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The decreasing validator rank bounds the current interval by the original
input budget, even after entering lists or restoring saved parent intervals. -/
theorem rlpValidation_input_bound (position stop : BitVec 64) (frames : List RlpValidationFrame)
    (inputLimit : Nat) (limitBound : inputLimit + 9 < 2^64)
    (rankBound : rlpValidationRank position stop frames ≤ 2 * inputLimit)
    (ordered : position.toNat ≤ stop.toNat) :
    (stop - position).toNat ≤ inputLimit ∧ (stop - position).toNat + 9 < 2^64 := by
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr ordered)]
  unfold rlpValidationRank at rankBound
  omega

/-- A normal original step uses and preserves a single input-sized rank budget;
its parser's non-wrapping input premise follows from that budget. -/
theorem rlpValidation_step_input_invariant {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (position stop scratch frame : BitVec 64) (frames : List RlpValidationFrame)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (topLocal : state.locals.lookup (ofString "top") = some (.val (.word (rlpValidationStackTop frames))))
    (stack : RlpValidationStack state.memory scratch.toNat frames)
    (intervals : RlpValidationIntervals position stop frames)
    (inputLimit : Nat) (limitBound : inputLimit + 9 < 2^64)
    (rankBound : rlpValidationRank position stop frames ≤ 2 * inputLimit)
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
      rlpValidationRank newPosition newStop newFrames ≤ 2 * inputLimit := by
  have ordered : position.toNat ≤ stop.toNat := by
    cases intervals with
    | nil _ _ ordered => exact ordered
    | cons _ _ _ _ ordered _ _ => exact ordered
  have inputBound := (rlpValidation_input_bound position stop frames inputLimit limitBound rankBound ordered).2
  have result := rlpValidation_step_arena_invariant state post position stop scratch frame frames
    positionLocal stopLocal topLocal stack intervals inputBound scratchGlobal frameGlobal code ticks
    orderedFrame framePositive ceiling scratchBelow stackCeiling arena flag flagLocal run
  rcases result with terminal | progressing
  · exact Or.inl terminal
  · obtain ⟨newPosition,newStop,frontier,newFrames,atPosition,atStop,atTop,validStack,validIntervals,decreases,cost⟩ := progressing
    exact Or.inr ⟨newPosition,newStop,frontier,newFrames,atPosition,atStop,atTop,validStack,validIntervals,decreases,cost,by omega⟩

#print axioms rlpValidation_input_bound
#print axioms rlpValidation_step_input_invariant
end InitECandidate.Runtime
