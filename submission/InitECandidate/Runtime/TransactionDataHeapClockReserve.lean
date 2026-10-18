import InitECandidate.Runtime.TransactionDataHeapWitness
import InitECandidate.Runtime.TransactionDataFieldBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual data-field call retains arbitrary future clock and heap reserves. -/
theorem transaction_decode_after_data_heap_clock_reserve {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (inside : valid.index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (headerBefore : tx.toNat + 200 < array.toNat)
    (futureTicks : Nat)
    (ticks : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634 + futureTicks ≤ state.clock)
    (run : evaluateHOLFiniteState state transactionDataField = (none,post)) :
    ∃ next : TransactionDecodeWitness post array count tx kind input inputLength scratch frame ceiling,
      next.index = valid.index + 1 ∧ next.heap = valid.heap ∧
      futureTicks ≤ post.clock := by
  have budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634 ≤ state.clock := by omega
  obtain ⟨next,indexEqual,heapEqual⟩ := transaction_decode_heap_witness_after_data state post array count tx kind input inputLength scratch frame ceiling inputLimit
    valid inside inputBound limitBound orderedFrame framePositive scratchBelow arrayFits arrayAbove headerBefore budget run
  have bounded := evaluate_transaction_data_field_bounded state array count valid.index input inputLength scratch frame ceiling inputLimit
    valid.arrayLocal valid.indexLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code
    orderedFrame framePositive scratchBelow valid.arena budget
  rw [run] at bounded
  dsimp only at bounded
  exact ⟨next,indexEqual,heapEqual,by have spent := bounded.1; omega⟩

#print axioms transaction_decode_after_data_heap_clock_reserve
end InitECandidate.Runtime
