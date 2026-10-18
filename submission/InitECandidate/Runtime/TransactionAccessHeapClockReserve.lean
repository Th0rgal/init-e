import InitECandidate.Runtime.TransactionAccessHeapWitness
import InitECandidate.Runtime.TransactionAccessBranchHeapBound
import InitECandidate.Runtime.TransactionAccessBranchGuardedHeapGrowth
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Space and source-clock reserves for later stages survive the actual access branch. -/
theorem transaction_decode_after_access_heap_clock_reserve {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (inside : valid.index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 32 < 2^64)
    (arrayAbove : ceiling ≤ array.toNat)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (headerBefore : tx.toNat + 216 < array.toNat)
    (futureTicks : Nat)
    (ticks : txListItemAccessCost inputLength.toNat + futureTicks ≤ state.clock)
    (run : evaluateHOLFiniteState state transactionAccessBranch = (none,post)) :
    ∃ next : TransactionDecodeWitness post array count tx kind input inputLength scratch frame ceiling,
      next.index = (if kind = 0#64 then valid.index else valid.index + 1) ∧
      valid.heap.toNat ≤ next.heap.toNat ∧
      futureTicks ≤ post.clock := by
  have budget : txListItemAccessCost inputLength.toNat ≤ state.clock := Nat.le_trans (Nat.le_add_right _ _) ticks
  obtain ⟨next,indexEqual,lower⟩ := transaction_decode_heap_witness_after_access state post array count tx kind input inputLength scratch frame ceiling inputLimit
    valid inside inputBound limitBound orderedFrame framePositive scratchBelow countLimit arrayAbove headerBefore inputBeforeFrame budget run
  obtain ⟨nextHeap,binding,upper,_,_,_,_⟩ := transaction_access_branch_normal_guarded_heap_growth state post array count valid.index input inputLength scratch frame valid.heap
    ceiling inputLimit valid.arrayLocal valid.indexLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code
    orderedFrame framePositive scratchBelow valid.arena valid.heapGlobal valid.heapBound countLimit valid.heapArena valid.inputBeforeHeap inputBeforeFrame (by have h := valid.arrayBeforeHeap; omega) valid.heapAligned budget run
  have same : next.heap = nextHeap := by
    exact HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (next.heapGlobal.symm.trans binding)))
  have bounded := evaluate_transaction_access_branch_heap_bounded state array valid.index input inputLength scratch frame valid.heap count.toNat ceiling inputLimit
    valid.arrayLocal valid.indexLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code
    orderedFrame framePositive scratchBelow valid.arena valid.heapGlobal valid.heapBound countLimit valid.heapArena valid.inputBeforeHeap inputBeforeFrame (by have h := valid.arrayBeforeHeap; omega) valid.heapAligned budget
  rw [run] at bounded
  dsimp only at bounded
  refine ⟨next,indexEqual,lower,?_⟩
  have spent := bounded.1
  omega

#print axioms transaction_decode_after_access_heap_clock_reserve
end InitECandidate.Runtime
