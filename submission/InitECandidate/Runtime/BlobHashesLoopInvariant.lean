import InitECandidate.Runtime.BlobHashesBufferLocal
import InitECandidate.Runtime.BlobHashesStepInputPrefix
import InitECandidate.Runtime.BlobHashesStepGlobals
import InitECandidate.Runtime.RlpSliceInputPrefixClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

structure BlobHashesLoopWitness {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count buffer input inputLength scratch frame : BitVec 64) (ceiling : Nat) where
  index : BitVec 64
  listLocal : state.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)])
  bufferLocal : state.locals.lookup (ofString "buf") = some (.val (.word buffer))
  indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index))
  indexBound : index.toNat ≤ count.toNat
  slices : RlpSliceInputPrefix state array input inputLength count.toNat
  scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch))
  frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame))
  code : state.code = originalRuntimeCode
  arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address

def BlobHashesLoopWitness.decClock {F : Type} {state : PanSemStateFiniteExact 64 F}
    {array count buffer input inputLength scratch frame : BitVec 64} {ceiling : Nat}
    (valid : BlobHashesLoopWitness state array count buffer input inputLength scratch frame ceiling) :
    BlobHashesLoopWitness (decClockHOLFinite state) array count buffer input inputLength scratch frame ceiling :=
  ⟨valid.index,valid.listLocal,valid.bufferLocal,valid.indexLocal,valid.indexBound,
    valid.slices.dec_clock state array input inputLength _,valid.scratchGlobal,valid.frameGlobal,valid.code,valid.arena⟩

/-- Actual normal blob iterations preserve all the runtime and slice premises
required by the next iteration. -/
theorem blobHashes_loop_witness_step {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count buffer input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : BlobHashesLoopWitness state array count buffer input inputLength scratch frame ceiling)
    (inside : valid.index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayBeforeFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (arrayBeforeBuffer : array.toNat + count.toNat * 16 ≤ buffer.toNat)
    (aligned : buffer.toNat % 8 = 0) (fits : buffer.toNat + count.toNat * 32 ≤ 2^64)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92650 ≤ state.clock)
    (run : evaluateHOLFiniteState state blobHashesStep = (none,post)) :
    ∃ next : BlobHashesLoopWitness post array count buffer input inputLength scratch frame ceiling,
      count.toNat - next.index.toNat < count.toNat - valid.index.toNat := by
  obtain ⟨atIndex,atList,indexBound,decreases⟩ := blobHashes_step_normal_progress state post valid.index count array
    valid.indexLocal valid.listLocal inside run
  have atBuffer := blobHashes_step_normal_buffer_local state post valid.index count array buffer valid.indexLocal valid.listLocal valid.bufferLocal run
  have globals := blobHashes_step_normal_globals state post array count valid.index buffer input inputLength scratch frame ceiling inputLimit
    valid.listLocal valid.bufferLocal valid.indexLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal
    valid.code orderedFrame framePositive scratchBelow valid.arena budget run
  have slices := blobHashes_step_normal_input_prefix state post array count valid.index buffer input inputLength scratch frame ceiling inputLimit
    valid.listLocal valid.bufferLocal valid.indexLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal
    valid.code orderedFrame framePositive scratchBelow valid.arena budget arrayBeforeFrame arrayBeforeBuffer aligned (by omega) run
  have metadata := evaluateHOLFiniteState_metadata state blobHashesStep
  rw [run] at metadata
  refine ⟨⟨valid.index + 1,atList,atBuffer,atIndex,indexBound,slices,globals.1,globals.2,metadata.1.trans valid.code,?_⟩,decreases⟩
  intro address lower upper
  rw [metadata.2.1]
  exact valid.arena address lower upper

#print axioms blobHashes_loop_witness_step
end InitECandidate.Runtime
