import InitECandidate.Runtime.TransactionAuthorizationHeapWitness
import InitECandidate.Runtime.TransactionAuthorizationBranchHeapBound
import InitECandidate.Runtime.TransactionAuthorizationBranchGuardedHeapGrowth
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual-layout authorization stage: the next transaction witness keeps every
runtime premise, the heap grows by at most the authorization workspace, and the
remaining clock covers any future cost. No frame reserve is assumed. -/
theorem transaction_decode_after_authorization_heap_clock {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (inside : valid.index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 120 < 2^64)
    (arrayAbove : ceiling ≤ array.toNat)
    (headerBefore : tx.toNat + 280 < array.toNat)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (futureTicks : Nat)
    (ticks : txListItemAuthorizationCost inputLength.toNat + futureTicks ≤ state.clock)
    (run : evaluateHOLFiniteState state transactionAuthorizationBranch = (none,post)) :
    ∃ next : TransactionDecodeWitness post array count tx kind input inputLength scratch frame ceiling,
      next.index = (if kind = 4#64 then valid.index + 1 else valid.index) ∧
      valid.heap.toNat ≤ next.heap.toNat ∧
      next.heap.toNat ≤ valid.heap.toNat + inputLength.toNat * 232 ∧ futureTicks ≤ post.clock := by
  have heapAbove : ceiling ≤ valid.heap.toNat := by have h := valid.arrayBeforeHeap; omega
  have budget : txListItemAuthorizationCost inputLength.toNat ≤ state.clock := Nat.le_trans (Nat.le_add_right _ _) ticks
  obtain ⟨next,indexEqual,lower⟩ := transaction_decode_heap_witness_after_authorization state post array count tx kind input inputLength scratch frame ceiling inputLimit
    valid inside inputBound limitBound orderedFrame framePositive scratchBelow countLimit arrayAbove headerBefore inputBeforeFrame budget run
  obtain ⟨nextHeap,binding,_,upper,_,_,_,_⟩ := transaction_authorization_branch_normal_guarded_heap_growth state post array count valid.index input inputLength scratch frame valid.heap
    ceiling inputLimit valid.arrayLocal valid.indexLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code
    orderedFrame framePositive scratchBelow valid.arena valid.heapGlobal valid.heapBound countLimit valid.heapArena valid.inputBeforeHeap inputBeforeFrame heapAbove valid.heapAligned budget run
  have same : next.heap = nextHeap := by
    exact HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (next.heapGlobal.symm.trans binding)))
  have bounded := evaluate_transaction_authorization_branch_heap_bounded state array valid.index input inputLength scratch frame valid.heap count.toNat ceiling inputLimit
    valid.arrayLocal valid.indexLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code
    orderedFrame framePositive scratchBelow valid.arena valid.heapGlobal valid.heapBound countLimit valid.heapArena valid.inputBeforeHeap inputBeforeFrame heapAbove valid.heapAligned budget
  rw [run] at bounded
  dsimp only at bounded
  refine ⟨next,indexEqual,lower,?_,?_⟩
  · rw [same]
    exact upper
  · have spent := bounded.1
    omega

#print axioms transaction_decode_after_authorization_heap_clock
end InitECandidate.Runtime
