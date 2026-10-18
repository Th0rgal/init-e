import InitECandidate.Runtime.TransactionDecodeWitness
import InitECandidate.Runtime.TransactionAccessBranchBound
import InitECandidate.Runtime.TransactionAccessBranchHeapGrowth
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Space and source-clock reserves for later stages survive the actual access branch. -/
theorem transaction_decode_after_access_reserves {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (inside : valid.index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 32 < 2^64)
    (arrayBeforeFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (headerBefore : tx.toNat + 216 < array.toNat)
    (futureSpace futureTicks : Nat)
    (futureWorkspace : inputLength.toNat * 32 + 7 ≤ futureSpace)
    (space : valid.heap.toNat + inputLength.toNat * 40 + (inputLength.toNat * 48 + 46) * inputLength.toNat + futureSpace ≤ frame.toNat)
    (ticks : txListItemAccessCost inputLength.toNat + futureTicks ≤ state.clock)
    (run : evaluateHOLFiniteState state transactionAccessBranch = (none,post)) :
    ∃ next : TransactionDecodeWitness post array count tx kind input inputLength scratch frame ceiling,
      next.index = (if kind = 0#64 then valid.index else valid.index + 1) ∧
      valid.heap.toNat ≤ next.heap.toNat ∧
      next.heap.toNat + futureSpace ≤ frame.toNat ∧ futureTicks ≤ post.clock := by
  have heapBeforeFrame : valid.heap.toNat + inputLength.toNat * 16 ≤ frame.toNat := by omega
  have reserve : valid.heap.toNat + inputLength.toNat * 40 + (inputLength.toNat * 48 + 46) * inputLength.toNat + inputLength.toNat * 32 + 7 ≤ frame.toNat := by omega
  have budget : txListItemAccessCost inputLength.toNat ≤ state.clock := Nat.le_trans (Nat.le_add_right _ _) ticks
  obtain ⟨next,indexEqual,lower⟩ := transaction_decode_witness_after_access state post array count tx kind input inputLength scratch frame ceiling inputLimit
    valid inside inputBound limitBound orderedFrame framePositive scratchBelow countLimit arrayBeforeFrame headerBefore heapBeforeFrame reserve budget run
  obtain ⟨nextHeap,binding,upper,_,_,_,_⟩ := transaction_access_branch_normal_heap_growth state post array count valid.index input inputLength scratch frame valid.heap
    ceiling inputLimit valid.arrayLocal valid.indexLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code
    orderedFrame framePositive scratchBelow valid.arena valid.heapGlobal valid.heapBound countLimit valid.heapArena valid.inputBeforeHeap heapBeforeFrame valid.heapAligned reserve budget run
  have same : next.heap = nextHeap := by
    exact HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (next.heapGlobal.symm.trans binding)))
  have bounded := evaluate_transaction_access_branch_bounded state array valid.index input inputLength scratch frame valid.heap count.toNat ceiling inputLimit
    valid.arrayLocal valid.indexLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code
    orderedFrame framePositive scratchBelow valid.arena valid.heapGlobal valid.heapBound countLimit valid.heapArena valid.inputBeforeHeap heapBeforeFrame valid.heapAligned reserve budget
  rw [run] at bounded
  dsimp only at bounded
  refine ⟨next,indexEqual,lower,?_,?_⟩
  · rw [same]
    omega
  · have spent := bounded.1
    omega

#print axioms transaction_decode_after_access_reserves
end InitECandidate.Runtime
