import InitECandidate.Runtime.TransactionToAdvanceHeapContinuationBound
import InitECandidate.Runtime.TransactionValueHeapContinuationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_to_value_heap_continuation_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (fields : valid.index.toNat + 2 ≤ count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (headerBefore : tx.toNat + 160 + 24 < array.toNat)
    (continuation : ProgHOL 64) (tailCost : Nat)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634 + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668 + tailCost) ≤ state.clock)
    (tailBound : ∀ middle : PanSemStateFiniteExact 64 F,
      ∀ next : TransactionDecodeWitness middle array count tx kind input inputLength scratch frame ceiling,
      next.index.toNat = valid.index.toNat + 2 → next.heap = valid.heap → tailCost ≤ middle.clock →
      let evaluated := evaluateHOLFiniteState middle continuation
      middle.clock ≤ evaluated.2.clock + tailCost ∧ evaluated.2.clock ≤ middle.clock ∧ evaluated.1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state (.seq transactionToField (.seq transactionIndexAdvance (.seq (transactionU256Field 160 transactionValueArguments) (.seq transactionIndexAdvance continuation))))
    state.clock ≤ evaluated.2.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634 + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668 + tailCost)) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have inside : valid.index.toNat < count.toNat := by omega
  apply transaction_to_advance_heap_continuation_bounded state array count tx kind input inputLength scratch frame ceiling inputLimit valid
    inside inputBound limitBound orderedFrame framePositive scratchBelow arrayFits arrayAbove (by omega)
    (.seq (transactionU256Field 160 transactionValueArguments) (.seq transactionIndexAdvance continuation))
    (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668 + tailCost) budget
  intro middle next indexEqual heapEqual ticks
  have nextInside : next.index.toNat < count.toNat := by omega
  apply transaction_value_heap_continuation_bounded middle array count tx kind input inputLength scratch frame ceiling inputLimit next
    nextInside inputBound limitBound orderedFrame framePositive scratchBelow arrayFits arrayAbove headerBefore continuation tailCost ticks
  intro output active activeIndex sameHeap remaining
  exact tailBound output active (by omega) (sameHeap.trans heapEqual) remaining

#print axioms transaction_to_value_heap_continuation_bounded
end InitECandidate.Runtime
