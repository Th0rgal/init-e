import InitECandidate.Runtime.RlpValidationStepInput
import InitECandidate.Runtime.RlpValidationStepFlag
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete normal-iteration state certificate for the original validator.
The clock reserve is a premise of each step rather than part of this invariant. -/
structure RlpValidationLoopWitness {F : Type} (state : PanSemStateFiniteExact 64 F)
    (frame : BitVec 64) (ceiling inputLimit : Nat) where
  position : BitVec 64
  stop : BitVec 64
  scratch : BitVec 64
  frames : List RlpValidationFrame
  flag : BitVec 64
  positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position))
  stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop))
  topLocal : state.locals.lookup (ofString "top") = some (.val (.word (rlpValidationStackTop frames)))
  flagLocal : state.locals.lookup (ofString "go") = some (.val (.word flag))
  stack : RlpValidationStack state.memory scratch.toNat frames
  intervals : RlpValidationIntervals position stop frames
  rankBound : rlpValidationRank position stop frames ≤ 2 * inputLimit
  scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch))
  frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame))
  code : state.code = originalRuntimeCode
  orderedFrame : frame ≤ scratch
  scratchBelow : scratch.toNat ≤ ceiling
  stackCeiling : RlpValidationStackCeiling ceiling frames
  arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address

/-- The full original normal step closes the iteration invariant or clears go.
In the continuing case rank strictly decreases and at most thirteen ticks pass. -/
theorem rlpValidation_loop_witness_step {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : RlpValidationLoopWitness state frame ceiling inputLimit)
    (limitBound : inputLimit + 9 < 2^64) (framePositive : 0 < frame.toNat)
    (ticks : 14 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpValidationStep = (none,post)) :
    post.locals.lookup (ofString "go") = some (.val (.word 0)) ∨
    ∃ next : RlpValidationLoopWitness post frame ceiling inputLimit,
      rlpValidationRank next.position next.stop next.frames <
        rlpValidationRank valid.position valid.stop valid.frames ∧ state.clock ≤ post.clock + 13 := by
  have result := rlpValidation_step_input_invariant state post valid.position valid.stop valid.scratch frame valid.frames
    valid.positionLocal valid.stopLocal valid.topLocal valid.stack valid.intervals inputLimit limitBound valid.rankBound
    valid.scratchGlobal valid.frameGlobal valid.code ticks valid.orderedFrame framePositive ceiling valid.scratchBelow
    valid.stackCeiling valid.arena valid.flag valid.flagLocal run
  rcases result with terminal | progressing
  · exact Or.inl terminal.1
  · have flagResult := rlpValidation_step_flag state post valid.position valid.stop valid.scratch frame valid.frames
      valid.positionLocal valid.stopLocal valid.topLocal valid.stack valid.scratchGlobal valid.frameGlobal valid.code ticks
      valid.orderedFrame ceiling valid.scratchBelow valid.stackCeiling valid.arena valid.flag valid.flagLocal run
    rcases flagResult with cleared | preserved
    · exact Or.inl cleared
    · obtain ⟨position,stop,scratch,frames,atPosition,atStop,atTop,stack,intervals,decreases,cost,
        rankBound,stackCeiling,scratchBelow,atScratch,atFrame,orderedFrame⟩ := progressing
      have metadata := evaluateHOLFiniteState_metadata state rlpValidationStep
      rw [run] at metadata
      refine Or.inr ⟨{
        position := position, stop := stop, scratch := scratch, frames := frames, flag := valid.flag
        positionLocal := atPosition, stopLocal := atStop, topLocal := atTop
        flagLocal := preserved.trans valid.flagLocal
        stack := stack, intervals := intervals, rankBound := rankBound
        scratchGlobal := atScratch, frameGlobal := atFrame, code := metadata.1.trans valid.code
        orderedFrame := orderedFrame, scratchBelow := scratchBelow, stackCeiling := stackCeiling
        arena := ?_ },decreases,cost⟩
      intro address lower upper
      rw [metadata.2.1]
      exact valid.arena address lower upper

#print axioms rlpValidation_loop_witness_step
end InitECandidate.Runtime
