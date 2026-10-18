import InitECandidate.Runtime.AccessListStepInputRuntimeContract
import InitECandidate.Runtime.AccessListStepInputOuterPrefix
import InitECandidate.Runtime.AccessListStepInputProgress
import InitECandidate.Runtime.RlpSliceInputPrefixClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Runtime premises retained between concrete authorization iterations. The
reserve covers all remaining iterations and one maximal parser workspace. -/
structure AccessLoopWitness {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count records input inputLength scratch frame : BitVec 64) (ceiling : Nat) where
  index : BitVec 64
  heap : BitVec 64
  listLocal : state.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)])
  recordsLocal : state.locals.lookup (ofString "recs") = some (.val (.word records))
  indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index))
  indexBound : index.toNat ≤ count.toNat
  slices : RlpSliceInputPrefix state array input inputLength count.toNat
  scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch))
  frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame))
  heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap))
  code : state.code = originalRuntimeCode
  arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address
  heapArena : ∀ address : BitVec 64, heap.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address
  heapBound : heap.toNat ≤ 33806089496
  heapAligned : heap.toNat % 8 = 0
  inputBeforeHeap : input.toNat + inputLength.toNat ≤ heap.toNat
  recordsBeforeHeap : records.toNat + count.toNat * 24 ≤ heap.toNat
  reserve : heap.toNat + (inputLength.toNat * 48 + 46) * (count.toNat - index.toNat) + inputLength.toNat * 32 + 7 ≤ frame.toNat

def AccessLoopWitness.decClock {F : Type} {state : PanSemStateFiniteExact 64 F}
    {array count records input inputLength scratch frame : BitVec 64} {ceiling : Nat}
    (valid : AccessLoopWitness state array count records input inputLength scratch frame ceiling) :
    AccessLoopWitness (decClockHOLFinite state) array count records input inputLength scratch frame ceiling :=
  ⟨valid.index,valid.heap,valid.listLocal,valid.recordsLocal,valid.indexLocal,valid.indexBound,
    valid.slices.dec_clock state array input inputLength _,valid.scratchGlobal,valid.frameGlobal,
    valid.heapGlobal,valid.code,valid.arena,valid.heapArena,valid.heapBound,valid.heapAligned,
    valid.inputBeforeHeap,valid.recordsBeforeHeap,valid.reserve⟩

/-- A successful original outer iteration retains its runtime premises and decreases rank. -/
theorem access_loop_witness_step {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count records input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : AccessLoopWitness state array count records input inputLength scratch frame ceiling)
    (inside : valid.index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 32 < 2^64)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (arrayBeforeFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (arrayBeforeRecords : array.toNat + count.toNat * 16 ≤ records.toNat)
    (budget : accessStepCost inputLength.toNat inputLength.toNat ≤ state.clock)
    (run : evaluateHOLFiniteState state accessStep = (none,post)) :
    ∃ next : AccessLoopWitness post array count records input inputLength scratch frame ceiling,
      count.toNat - next.index.toNat < count.toNat - valid.index.toNat := by
  have recordsBound := valid.recordsBeforeHeap
  have heapBound := valid.heapBound
  have product : (valid.index * 24#64).toNat = valid.index.toNat * 24 := by
    apply BitVec.toNat_mul_of_lt
    change valid.index.toNat * 24 < 2^64
    omega
  have recordNat : (records + valid.index * 24#64).toNat = records.toNat + valid.index.toNat * 24 := by
    rw [BitVec.toNat_add_of_lt (by rw [product]; omega),product]
  have recordFits : (records + valid.index * 24#64).toNat + 24 < 2^64 := by rw [recordNat]; omega
  have reserve := valid.reserve
  have arraySpace : valid.heap.toNat + inputLength.toNat * 16 ≤ frame.toNat := by omega
  have parserSpace : valid.heap.toNat + inputLength.toNat * 32 + 7 ≤ frame.toNat := by omega
  obtain ⟨nextHeap,heapFinal,scratchFinal,frameFinal,low,high,endBound,endAligned⟩ :=
    access_step_input_heap_bounds state post valid.index array count input inputLength scratch frame valid.heap ceiling inputLimit
      valid.indexLocal valid.listLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code
      orderedFrame framePositive scratchBelow valid.arena valid.heapGlobal valid.heapBound countLimit valid.heapArena
      inputBeforeFrame valid.inputBeforeHeap arraySpace parserSpace budget run
  have slices := access_step_input_outer_prefix state post valid.index array count input inputLength scratch frame valid.heap ceiling inputLimit
    valid.indexLocal valid.listLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code
    orderedFrame framePositive scratchBelow valid.arena valid.heapGlobal valid.heapBound countLimit valid.heapArena
    inputBeforeFrame valid.inputBeforeHeap arraySpace parserSpace budget records valid.recordsLocal arrayBeforeFrame
    (by omega) (by rw [recordNat]; omega) recordFits run
  obtain ⟨advanced,listSame,recordsSame,nextNat,decreases⟩ := access_step_input_progress state post valid.index array count input inputLength scratch frame valid.heap ceiling inputLimit
    valid.indexLocal valid.listLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code
    orderedFrame framePositive scratchBelow valid.arena valid.heapGlobal valid.heapBound countLimit valid.heapArena
    inputBeforeFrame valid.inputBeforeHeap arraySpace parserSpace budget run
  have metadata := evaluateHOLFiniteState_metadata state accessStep
  rw [run] at metadata
  refine ⟨⟨valid.index + 1,nextHeap,listSame.trans valid.listLocal,recordsSame.trans valid.recordsLocal,advanced,
    by rw [nextNat]; omega,slices,scratchFinal,frameFinal,heapFinal,metadata.1.trans valid.code,
    ?_,?_,endBound,endAligned,?_,?_,?_⟩,?_⟩
  · intro address lower upper
    rw [metadata.2.1]
    exact valid.arena address lower upper
  · intro address lower upper
    rw [metadata.2.1]
    exact valid.heapArena address (Nat.le_trans low lower) upper
  · exact Nat.le_trans valid.inputBeforeHeap low
  · exact Nat.le_trans valid.recordsBeforeHeap low
  · rw [nextNat]
    have rankSplit : count.toNat - valid.index.toNat = (count.toNat - (valid.index.toNat + 1)) + 1 := by omega
    rw [rankSplit,Nat.mul_add,Nat.mul_one] at reserve
    omega
  · simpa only [accessRank,valid.indexLocal,advanced] using decreases

#print axioms AccessLoopWitness.decClock
#print axioms access_loop_witness_step
end InitECandidate.Runtime
