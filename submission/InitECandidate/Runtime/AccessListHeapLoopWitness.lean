import InitECandidate.Runtime.AccessListStepInputHeapRuntimeContract
import InitECandidate.Runtime.AccessListStepInputHeapIndependentOuterPrefix
import InitECandidate.Runtime.AccessListStepInputHeapProgress
import InitECandidate.Runtime.RlpSliceInputPrefixClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Runtime premises retained between actual access-list iterations. Heap
capacity follows from completed allocations; no future reserve is assumed. -/
structure AccessHeapLoopWitness {F : Type} (state : PanSemStateFiniteExact 64 F)
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

def AccessHeapLoopWitness.decClock {F : Type} {state : PanSemStateFiniteExact 64 F}
    {array count records input inputLength scratch frame : BitVec 64} {ceiling : Nat}
    (valid : AccessHeapLoopWitness state array count records input inputLength scratch frame ceiling) :
    AccessHeapLoopWitness (decClockHOLFinite state) array count records input inputLength scratch frame ceiling :=
  ⟨valid.index,valid.heap,valid.listLocal,valid.recordsLocal,valid.indexLocal,valid.indexBound,
    valid.slices.dec_clock state array input inputLength _,valid.scratchGlobal,valid.frameGlobal,
    valid.heapGlobal,valid.code,valid.arena,valid.heapArena,valid.heapBound,valid.heapAligned,
    valid.inputBeforeHeap,valid.recordsBeforeHeap⟩

/-- A successful original outer iteration retains its runtime premises and decreases rank. -/
theorem access_heap_loop_witness_step {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count records input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : AccessHeapLoopWitness state array count records input inputLength scratch frame ceiling)
    (inside : valid.index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 32 < 2^64)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (arrayAbove : ceiling ≤ array.toNat)
    (arrayBeforeRecords : array.toNat + count.toNat * 16 ≤ records.toNat)
    (budget : accessStepCost inputLength.toNat inputLength.toNat ≤ state.clock)
    (run : evaluateHOLFiniteState state accessStep = (none,post)) :
    ∃ next : AccessHeapLoopWitness post array count records input inputLength scratch frame ceiling,
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
  have heapAbove : ceiling ≤ valid.heap.toNat := by
    have recordsEnd := valid.recordsBeforeHeap
    omega
  obtain ⟨nextHeap,heapFinal,scratchFinal,frameFinal,low,high,endBound,endAligned⟩ :=
    access_step_input_guarded_heap_bounds state post valid.index array count input inputLength scratch frame valid.heap ceiling inputLimit
      valid.indexLocal valid.listLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code
      orderedFrame framePositive scratchBelow valid.arena valid.heapGlobal valid.heapBound countLimit valid.heapArena
      inputBeforeFrame valid.inputBeforeHeap heapAbove budget run
  have slices := access_step_input_heap_independent_outer_prefix state post valid.index array count input inputLength scratch frame valid.heap ceiling inputLimit
    valid.indexLocal valid.listLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code
    orderedFrame framePositive scratchBelow valid.arena valid.heapGlobal valid.heapBound countLimit valid.heapArena
    inputBeforeFrame valid.inputBeforeHeap budget array count input inputLength valid.slices records valid.recordsLocal arrayAbove
    (by omega) (by rw [recordNat]; omega) recordFits run
  obtain ⟨advanced,listSame,recordsSame,nextNat,decreases⟩ := access_step_input_heap_progress state post valid.index array count input inputLength scratch frame valid.heap ceiling inputLimit
    valid.indexLocal valid.listLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code
    orderedFrame framePositive scratchBelow valid.arena valid.heapGlobal valid.heapBound countLimit valid.heapArena
    inputBeforeFrame valid.inputBeforeHeap heapAbove budget run
  have metadata := evaluateHOLFiniteState_metadata state accessStep
  rw [run] at metadata
  refine ⟨⟨valid.index + 1,nextHeap,listSame.trans valid.listLocal,recordsSame.trans valid.recordsLocal,advanced,
    by rw [nextNat]; omega,slices,scratchFinal,frameFinal,heapFinal,metadata.1.trans valid.code,
    ?_,?_,endBound,endAligned,?_,?_⟩,?_⟩
  · intro address lower upper
    rw [metadata.2.1]
    exact valid.arena address lower upper
  · intro address lower upper
    rw [metadata.2.1]
    exact valid.heapArena address (Nat.le_trans low lower) upper
  · exact Nat.le_trans valid.inputBeforeHeap low
  · exact Nat.le_trans valid.recordsBeforeHeap low
  · simpa only [accessRank,valid.indexLocal,advanced] using decreases

#print axioms AccessHeapLoopWitness.decClock
#print axioms access_heap_loop_witness_step
end InitECandidate.Runtime
