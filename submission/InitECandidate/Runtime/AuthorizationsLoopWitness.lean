import InitECandidate.Runtime.AuthorizationsStepInputFixedHeap
import InitECandidate.Runtime.AuthorizationsStepInputPrefix
import InitECandidate.Runtime.AuthorizationsStepLocalFrame
import InitECandidate.Runtime.AuthorizationsStepProgress
import InitECandidate.Runtime.AuthorizationsHeapAdvance
import InitECandidate.Runtime.RlpSliceInputPrefixClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Runtime premises retained between concrete authorization iterations. The
reserve covers all remaining 96-byte arrays and one maximal inner array. -/
structure AuthorizationsLoopWitness {F : Type} (state : PanSemStateFiniteExact 64 F)
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
  recordsBeforeHeap : records.toNat + count.toNat * 120 ≤ heap.toNat
  reserve : heap.toNat + 96 * (count.toNat - index.toNat) + inputLength.toNat * 16 ≤ frame.toNat

def AuthorizationsLoopWitness.decClock {F : Type} {state : PanSemStateFiniteExact 64 F}
    {array count records input inputLength scratch frame : BitVec 64} {ceiling : Nat}
    (valid : AuthorizationsLoopWitness state array count records input inputLength scratch frame ceiling) :
    AuthorizationsLoopWitness (decClockHOLFinite state) array count records input inputLength scratch frame ceiling :=
  ⟨valid.index,valid.heap,valid.listLocal,valid.recordsLocal,valid.indexLocal,valid.indexBound,
    valid.slices.dec_clock state array input inputLength _,valid.scratchGlobal,valid.frameGlobal,
    valid.heapGlobal,valid.code,valid.arena,valid.heapArena,valid.heapBound,valid.heapAligned,
    valid.inputBeforeHeap,valid.recordsBeforeHeap,valid.reserve⟩

/-- Every normally completed actual iteration preserves the next iteration's
runtime premises and decreases the remaining-entry rank. -/
theorem authorizations_loop_witness_step {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count records input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : AuthorizationsLoopWitness state array count records input inputLength scratch frame ceiling)
    (inside : valid.index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 16 < 2^64)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (arrayBeforeFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (arrayBeforeRecords : array.toNat + count.toNat * 16 ≤ records.toNat)
    (budget : authorizationStepCost inputLength.toNat inputLength.toNat ≤ state.clock)
    (run : evaluateHOLFiniteState state authorizationStep = (none,post)) :
    ∃ next : AuthorizationsLoopWitness post array count records input inputLength scratch frame ceiling,
      count.toNat - next.index.toNat < count.toNat - valid.index.toNat := by
  let record := records + valid.index * 120#64
  have product : (valid.index * 120#64).toNat = valid.index.toNat * 120 := by
    apply BitVec.toNat_mul_of_lt
    have bound := valid.recordsBeforeHeap
    have heapBound := valid.heapBound
    change valid.index.toNat * 120 < 2^64
    omega
  have recordNat : record.toNat = records.toNat + valid.index.toNat * 120 := by
    dsimp only [record]
    rw [BitVec.toNat_add_of_lt (by rw [product]; have b := valid.recordsBeforeHeap; have h := valid.heapBound; omega),product]
  have recordBeforeHeap : record.toNat + 120 ≤ valid.heap.toNat := by
    rw [recordNat]
    have bound := valid.recordsBeforeHeap
    omega
  have recordFits : record.toNat + 120 < 2^64 := by have h := valid.heapBound; omega
  have heapBeforeFrame : valid.heap.toNat + inputLength.toNat * 16 ≤ frame.toNat := by
    have reserve := valid.reserve
    omega
  have runtime := authorization_step_input_normal_fixed_heap state post record records valid.index array count input inputLength scratch frame valid.heap
    ceiling inputLimit rfl valid.recordsLocal valid.indexLocal valid.listLocal valid.slices inside inputBound limitBound
    valid.scratchGlobal valid.frameGlobal valid.code orderedFrame framePositive scratchBelow valid.arena valid.heapGlobal
    valid.heapBound countLimit valid.heapArena inputBeforeFrame valid.inputBeforeHeap heapBeforeFrame recordBeforeHeap recordFits budget run
  have slices := authorization_step_input_normal_prefix state post record records valid.index array count input inputLength scratch frame valid.heap
    ceiling inputLimit rfl valid.recordsLocal valid.indexLocal valid.listLocal valid.slices inside inputBound limitBound
    valid.scratchGlobal valid.frameGlobal valid.code orderedFrame framePositive scratchBelow valid.arena valid.heapGlobal
    valid.heapBound countLimit valid.heapArena inputBeforeFrame valid.inputBeforeHeap heapBeforeFrame recordBeforeHeap recordFits budget
    arrayBeforeFrame (by rw [recordNat]; have b := arrayBeforeRecords; omega) run
  obtain ⟨advanced,nextNat,decreases⟩ := evaluate_authorization_step_rank_progress state post valid.index count valid.indexLocal inside run
  have locals := evaluate_authorization_step_loop_locals state post run
  have metadata := evaluateHOLFiniteState_metadata state authorizationStep
  rw [run] at metadata
  have heapNat := authorization_heap_advance valid.heap runtime.2.2.2.1 valid.heapAligned
  have nextBound : (valid.index + 1).toNat ≤ count.toNat := by rw [nextNat]; omega
  refine ⟨⟨valid.index + 1,allocationEnd valid.heap 96,locals.1.trans valid.listLocal,
    locals.2.trans valid.recordsLocal,advanced,nextBound,slices,runtime.2.1,runtime.2.2.1,runtime.1,
    metadata.1.trans valid.code,?_,?_,runtime.2.2.2.2.1,runtime.2.2.2.2.2,?_,?_,?_⟩,?_⟩
  · intro address lower upper
    rw [metadata.2.1]
    exact valid.arena address lower upper
  · intro address lower upper
    rw [metadata.2.1]
    apply valid.heapArena address (by rw [heapNat] at lower; omega) upper
  · rw [heapNat]
    have bound := valid.inputBeforeHeap
    omega
  · rw [heapNat]
    have bound := valid.recordsBeforeHeap
    omega
  · rw [heapNat,nextNat]
    have reserve := valid.reserve
    omega
  · simpa only [authorizationRank,valid.indexLocal,advanced] using decreases

#print axioms AuthorizationsLoopWitness.decClock
#print axioms authorizations_loop_witness_step
end InitECandidate.Runtime
