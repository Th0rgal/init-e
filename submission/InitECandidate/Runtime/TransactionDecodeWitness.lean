import InitECandidate.Runtime.TransactionAccessBranchPrefix
import InitECandidate.Runtime.TransactionAccessBranchHeapLowerBound
import InitECandidate.Runtime.TransactionAccessLocalProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Runtime premises shared between concrete transaction decoder field stages. -/
structure TransactionDecodeWitness {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling : Nat) where
  index : BitVec 64
  heap : BitVec 64
  arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array))
  txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx))
  typeLocal : state.locals.lookup (ofString "t") = some (.val (.word kind))
  indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index))
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
  arrayBeforeHeap : array.toNat + count.toNat * 16 ≤ heap.toNat

/-- The actual access conditional retains the next transaction stage's runtime premises. -/
theorem transaction_decode_witness_after_access {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (inside : valid.index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 32 < 2^64)
    (arrayBeforeFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (headerBefore : tx.toNat + 216 < array.toNat)
    (heapBeforeFrame : valid.heap.toNat + inputLength.toNat * 16 ≤ frame.toNat)
    (reserve : valid.heap.toNat + inputLength.toNat * 40 + (inputLength.toNat * 48 + 46) * inputLength.toNat + inputLength.toNat * 32 + 7 ≤ frame.toNat)
    (budget : txListItemAccessCost inputLength.toNat ≤ state.clock)
    (run : evaluateHOLFiniteState state transactionAccessBranch = (none,post)) :
    ∃ next : TransactionDecodeWitness post array count tx kind input inputLength scratch frame ceiling,
      next.index = (if kind = 0#64 then valid.index else valid.index + 1) ∧ valid.heap.toNat ≤ next.heap.toNat := by
  have retained := transaction_access_branch_normal_prefix state post array count valid.index tx input inputLength scratch frame valid.heap ceiling inputLimit
    valid.arrayLocal valid.indexLocal valid.txLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code
    orderedFrame framePositive scratchBelow valid.arena valid.heapGlobal valid.heapBound countLimit valid.heapArena valid.inputBeforeHeap heapBeforeFrame
    arrayBeforeFrame valid.arrayBeforeHeap headerBefore valid.heapAligned reserve budget run
  obtain ⟨nextHeap,heapFinal,lower,heapLimit,aligned,scratchFinal,frameFinal⟩ := transaction_access_branch_normal_heap_lower_bound state post
    array count valid.index input inputLength scratch frame valid.heap ceiling inputLimit valid.arrayLocal valid.indexLocal valid.slices inside inputBound limitBound
    valid.scratchGlobal valid.frameGlobal valid.code orderedFrame framePositive scratchBelow valid.arena valid.heapGlobal valid.heapBound countLimit valid.heapArena
    valid.inputBeforeHeap heapBeforeFrame valid.heapAligned reserve budget run
  have locals := transaction_access_branch_other_local state post
  have advanced := transaction_access_branch_index state post kind valid.index valid.typeLocal valid.indexLocal run
  have metadata := evaluateHOLFiniteState_metadata state transactionAccessBranch
  rw [run] at metadata
  have nextNat : (valid.index + 1).toNat = valid.index.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change valid.index.toNat + 1 < 2^64; omega)]
    rfl
  refine ⟨⟨if kind = 0#64 then valid.index else valid.index + 1,nextHeap,
    (locals _ (by decide) run).trans valid.arrayLocal,(locals _ (by decide) run).trans valid.txLocal,
    (locals _ (by decide) run).trans valid.typeLocal,advanced,?_,retained,scratchFinal,frameFinal,heapFinal,
    metadata.1.trans valid.code,?_,?_,heapLimit,aligned,Nat.le_trans valid.inputBeforeHeap lower,
    Nat.le_trans valid.arrayBeforeHeap lower⟩,rfl,lower⟩
  · split
    · exact Nat.le_of_lt inside
    · rw [nextNat]; omega
  · intro address low high
    rw [metadata.2.1]
    exact valid.arena address low high
  · intro address low high
    rw [metadata.2.1]
    exact valid.heapArena address (Nat.le_trans lower low) high

#print axioms transaction_decode_witness_after_access
end InitECandidate.Runtime
