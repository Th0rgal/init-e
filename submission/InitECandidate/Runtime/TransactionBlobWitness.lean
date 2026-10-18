import InitECandidate.Runtime.TransactionDecodeWitness
import InitECandidate.Runtime.TransactionBlobBranchPrefix
import InitECandidate.Runtime.TransactionBlobBranchHeapGrowth
import InitECandidate.Runtime.TransactionBlobLocalFrame
import InitECandidate.Runtime.TransactionBlobLocalProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- The actual blob conditional retains the next transaction stage's runtime premises. -/
theorem transaction_decode_witness_after_blob {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (fields : valid.index.toNat + 2 ≤ count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 32 < 2^64)
    (arrayBeforeFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (headerBefore : tx.toNat + 264 < array.toNat)
    (heapBeforeFrame : valid.heap.toNat + inputLength.toNat * 16 ≤ frame.toNat)
    (budget : (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) + txListItemBlobCost inputLength.toNat ≤ state.clock)
    (run : evaluateHOLFiniteState state transactionBlobBranch = (none,post)) :
    ∃ next : TransactionDecodeWitness post array count tx kind input inputLength scratch frame ceiling,
      next.index = (if kind = 3#64 then valid.index + 2 else valid.index) ∧ valid.heap.toNat ≤ next.heap.toNat := by
  have nextNat : (valid.index + 1).toNat = valid.index.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change valid.index.toNat + 1 < 2^64; omega)]
    rfl
  have inside : (valid.index + 1).toNat < count.toNat := by rw [nextNat]; omega
  have middleInside : valid.index.toNat < count.toNat := by omega
  have retained := transaction_blob_branch_normal_prefix state post array count valid.index tx input inputLength scratch frame valid.heap ceiling inputLimit
    valid.arrayLocal valid.indexLocal valid.slices inside middleInside valid.txLocal (by omega) arrayBeforeFrame inputBound limitBound
    valid.scratchGlobal valid.frameGlobal valid.code orderedFrame framePositive scratchBelow valid.arena valid.heapGlobal valid.heapBound countLimit
    valid.heapArena valid.inputBeforeHeap heapBeforeFrame budget valid.arrayBeforeHeap headerBefore valid.heapAligned run
  obtain ⟨nextHeap,heapFinal,lower,growth,heapLimit,aligned,scratchFinal,frameFinal⟩ := transaction_blob_branch_normal_heap_growth state post
    array count valid.index tx input inputLength scratch frame valid.heap ceiling inputLimit valid.arrayLocal valid.indexLocal valid.slices inside middleInside
    valid.txLocal (by omega) arrayBeforeFrame inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code orderedFrame framePositive scratchBelow
    valid.arena valid.heapGlobal valid.heapBound countLimit valid.heapArena valid.inputBeforeHeap heapBeforeFrame budget valid.heapAligned run
  have locals := transaction_blob_branch_other_local state post
  have advanced := transaction_blob_branch_index state post kind valid.index valid.typeLocal valid.indexLocal run
  have metadata := evaluateHOLFiniteState_metadata state transactionBlobBranch
  rw [run] at metadata
  have finalNat : (valid.index + 2).toNat = valid.index.toNat + 2 := by
    rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change valid.index.toNat + 2 < 2^64; omega)]
    rfl
  refine ⟨⟨if kind = 3#64 then valid.index + 2 else valid.index,nextHeap,
    (locals _ (by decide) (by decide) run).trans valid.arrayLocal,(locals _ (by decide) (by decide) run).trans valid.txLocal,
    (locals _ (by decide) (by decide) run).trans valid.typeLocal,advanced,?_,retained,scratchFinal,frameFinal,heapFinal,
    metadata.1.trans valid.code,?_,?_,heapLimit,aligned,Nat.le_trans valid.inputBeforeHeap lower,
    Nat.le_trans valid.arrayBeforeHeap lower⟩,rfl,lower⟩
  · split
    · rw [finalNat]; exact fields
    · exact valid.indexBound
  · intro address low high
    rw [metadata.2.1]
    exact valid.arena address low high
  · intro address low high
    rw [metadata.2.1]
    exact valid.heapArena address (Nat.le_trans lower low) high

#print axioms transaction_decode_witness_after_blob
end InitECandidate.Runtime
