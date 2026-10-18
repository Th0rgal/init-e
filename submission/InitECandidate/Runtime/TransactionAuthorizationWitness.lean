import InitECandidate.Runtime.TransactionDecodeWitness
import InitECandidate.Runtime.TransactionAuthorizationBranchPrefix
import InitECandidate.Runtime.TransactionAuthorizationBranchHeapGrowth
import InitECandidate.Runtime.TransactionAuthorizationLocalProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- The actual access conditional retains the next transaction stage's runtime premises. -/
theorem transaction_decode_witness_after_authorization {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (inside : valid.index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 120 < 2^64)
    (arrayBeforeFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (headerBefore : tx.toNat + 280 < array.toNat)
    (heapBeforeFrame : valid.heap.toNat + inputLength.toNat * 16 ≤ frame.toNat)
    (reserve : valid.heap.toNat + inputLength.toNat * 248 ≤ frame.toNat)
    (budget : txListItemAuthorizationCost inputLength.toNat ≤ state.clock)
    (run : evaluateHOLFiniteState state transactionAuthorizationBranch = (none,post)) :
    ∃ next : TransactionDecodeWitness post array count tx kind input inputLength scratch frame ceiling,
      next.index = (if kind = 4#64 then valid.index + 1 else valid.index) ∧ valid.heap.toNat ≤ next.heap.toNat := by
  have retained := transaction_authorization_branch_normal_prefix state post array count valid.index tx input inputLength scratch frame valid.heap ceiling inputLimit
    valid.arrayLocal valid.indexLocal valid.txLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code
    orderedFrame framePositive scratchBelow valid.arena valid.heapGlobal valid.heapBound countLimit valid.heapArena valid.inputBeforeHeap heapBeforeFrame
    arrayBeforeFrame valid.arrayBeforeHeap headerBefore valid.heapAligned reserve budget run
  obtain ⟨nextHeap,heapFinal,lower,_,heapLimit,aligned,scratchFinal,frameFinal⟩ := transaction_authorization_branch_normal_heap_growth state post
    array count valid.index input inputLength scratch frame valid.heap ceiling inputLimit valid.arrayLocal valid.indexLocal valid.slices inside inputBound limitBound
    valid.scratchGlobal valid.frameGlobal valid.code orderedFrame framePositive scratchBelow valid.arena valid.heapGlobal valid.heapBound countLimit valid.heapArena
    valid.inputBeforeHeap heapBeforeFrame valid.heapAligned reserve budget run
  have locals := transaction_authorization_branch_other_local state post
  have advanced := transaction_authorization_branch_index state post kind valid.index valid.typeLocal valid.indexLocal run
  have metadata := evaluateHOLFiniteState_metadata state transactionAuthorizationBranch
  rw [run] at metadata
  have nextNat : (valid.index + 1).toNat = valid.index.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change valid.index.toNat + 1 < 2^64; omega)]
    rfl
  refine ⟨⟨if kind = 4#64 then valid.index + 1 else valid.index,nextHeap,
    (locals _ (by decide) run).trans valid.arrayLocal,(locals _ (by decide) run).trans valid.txLocal,
    (locals _ (by decide) run).trans valid.typeLocal,advanced,?_,retained,scratchFinal,frameFinal,heapFinal,
    metadata.1.trans valid.code,?_,?_,heapLimit,aligned,Nat.le_trans valid.inputBeforeHeap lower,
    Nat.le_trans valid.arrayBeforeHeap lower⟩,rfl,lower⟩
  · split
    · rw [nextNat]; omega
    · exact valid.indexBound
  · intro address low high
    rw [metadata.2.1]
    exact valid.arena address low high
  · intro address low high
    rw [metadata.2.1]
    exact valid.heapArena address (Nat.le_trans lower low) high

#print axioms transaction_decode_witness_after_authorization
end InitECandidate.Runtime
