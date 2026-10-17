import InitECandidate.Runtime.RlpListCountInvariant
import InitECandidate.Runtime.RlpListCountStepGlobals
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Full original list-counting loop certificate, with fixed input and scratch
arena and dynamic count/offset locals. -/
structure RlpListCountLoopWitness {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling : Nat) where
  offset : BitVec 64
  count : BitVec 64
  pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer))
  lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length))
  offsetLocal : state.locals.lookup (ofString "off") = some (.val (.word offset))
  countLocal : state.locals.lookup (ofString "count") = some (.val (.word count))
  countBound : count.toNat ≤ offset.toNat
  offsetBound : offset.toNat ≤ length.toNat
  scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch))
  frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame))
  code : state.code = originalRuntimeCode
  arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address

def RlpListCountLoopWitness.decClock {F : Type} {state : PanSemStateFiniteExact 64 F}
    {pointer length scratch frame : BitVec 64} {ceiling : Nat}
    (valid : RlpListCountLoopWitness state pointer length scratch frame ceiling) :
    RlpListCountLoopWitness (decClockHOLFinite state) pointer length scratch frame ceiling := {valid with}

/-- Normal original list-count iterations close the full invariant and strictly
decrease remaining input, including scratch restoration and arena metadata. -/
theorem rlpListCount_loop_witness_step {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : RlpListCountLoopWitness state pointer length scratch frame ceiling)
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (budget : (2 * length.toNat + 1) * 15 + 18 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpListCountStep = (none,post)) :
    ∃ next : RlpListCountLoopWitness post pointer length scratch frame ceiling,
      length.toNat - next.offset.toNat < length.toNat - valid.offset.toNat := by
  obtain ⟨offset,count,atOffset,atCount,atPointer,atLength,countBound,offsetBound,decreases⟩ :=
    rlpListCount_step_invariant state post pointer length valid.offset valid.count valid.pointerLocal valid.lengthLocal
      valid.offsetLocal valid.countLocal valid.countBound valid.offsetBound valid.code (by omega) run
  have globals := rlpListCount_normal_step_globals state post pointer length valid.offset scratch frame ceiling inputLimit
    valid.pointerLocal valid.lengthLocal valid.offsetLocal valid.offsetBound noWrap lengthBound limitBound valid.scratchGlobal
    valid.frameGlobal valid.code orderedFrame framePositive scratchBelow valid.arena budget run
  have metadata := evaluateHOLFiniteState_metadata state rlpListCountStep
  rw [run] at metadata
  refine ⟨{
    offset := offset, count := count, pointerLocal := atPointer, lengthLocal := atLength
    offsetLocal := atOffset, countLocal := atCount, countBound := countBound, offsetBound := offsetBound
    scratchGlobal := globals.1, frameGlobal := globals.2, code := metadata.1.trans valid.code
    arena := ?_ },decreases⟩
  intro address lower upper
  rw [metadata.2.1]
  exact valid.arena address lower upper

#print axioms rlpListCount_loop_witness_step
end InitECandidate.Runtime
