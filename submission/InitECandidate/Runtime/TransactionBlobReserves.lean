import InitECandidate.Runtime.TransactionBlobWitness
import InitECandidate.Runtime.TransactionBlobBranchBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem transaction_decode_after_blob_reserves {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (fields : valid.index.toNat + 2 ≤ count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 32 < 2^64)
    (arrayBeforeFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (headerBefore : tx.toNat + 264 < array.toNat)
    (futureSpace futureTicks : Nat)
    (space : valid.heap.toNat + inputLength.toNat * 48 + futureSpace ≤ frame.toNat)
    (ticks : (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) + txListItemBlobCost inputLength.toNat + futureTicks ≤ state.clock)
    (run : evaluateHOLFiniteState state transactionBlobBranch = (none,post)) :
    ∃ next : TransactionDecodeWitness post array count tx kind input inputLength scratch frame ceiling,
      next.index = (if kind = 3#64 then valid.index + 2 else valid.index) ∧ valid.heap.toNat ≤ next.heap.toNat ∧
      next.heap.toNat + futureSpace ≤ frame.toNat ∧ futureTicks ≤ post.clock := by
  let cost := (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) + txListItemBlobCost inputLength.toNat
  have budget : cost ≤ state.clock := by omega
  have heapBeforeFrame : valid.heap.toNat + inputLength.toNat * 16 ≤ frame.toNat := by omega
  obtain ⟨next,indexEqual,lower⟩ := transaction_decode_witness_after_blob state post array count tx kind input inputLength scratch frame ceiling inputLimit
    valid fields inputBound limitBound orderedFrame framePositive scratchBelow countLimit arrayBeforeFrame headerBefore heapBeforeFrame budget run
  have shifted : (valid.index + 1).toNat = valid.index.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change valid.index.toNat + 1 < 2^64; omega)]
    rfl
  have inside : (valid.index + 1).toNat < count.toNat := by rw [shifted]; omega
  have middleInside : valid.index.toNat < count.toNat := by omega
  obtain ⟨nextHeap,binding,_,upper,_,_,_,_⟩ := transaction_blob_branch_normal_heap_growth state post
    array count valid.index tx input inputLength scratch frame valid.heap ceiling inputLimit valid.arrayLocal valid.indexLocal valid.slices inside middleInside
    valid.txLocal (by omega) arrayBeforeFrame inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code orderedFrame framePositive scratchBelow
    valid.arena valid.heapGlobal valid.heapBound countLimit valid.heapArena valid.inputBeforeHeap heapBeforeFrame budget valid.heapAligned run
  have same : next.heap = nextHeap :=
    HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (next.heapGlobal.symm.trans binding)))
  have bounded := evaluate_transaction_blob_branch_bounded state array count valid.index tx input inputLength scratch frame valid.heap ceiling inputLimit
    valid.arrayLocal valid.indexLocal valid.slices inside middleInside valid.txLocal (by omega) arrayBeforeFrame inputBound limitBound
    valid.scratchGlobal valid.frameGlobal valid.code orderedFrame framePositive scratchBelow valid.arena valid.heapGlobal valid.heapBound countLimit
    valid.heapArena valid.inputBeforeHeap heapBeforeFrame budget
  rw [run] at bounded
  dsimp only at bounded
  refine ⟨next,indexEqual,lower,?_,?_⟩
  · rw [same]; omega
  · have spent := bounded.1; dsimp [cost] at budget; omega

#print axioms transaction_decode_after_blob_reserves
end InitECandidate.Runtime
