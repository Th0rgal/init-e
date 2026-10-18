import InitECandidate.Runtime.TransactionToHeapContinuationBound
import InitECandidate.Runtime.TransactionIndexHeapContinuationBound
import InitECandidate.Runtime.TransactionToFieldBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_to_advance_heap_continuation_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (inside : valid.index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (headerBefore : tx.toNat + 152 < array.toNat)
    (continuation : ProgHOL 64) (tailCost : Nat)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634 + tailCost ≤ state.clock)
    (tailBound : ∀ middle : PanSemStateFiniteExact 64 F,
      ∀ next : TransactionDecodeWitness middle array count tx kind input inputLength scratch frame ceiling,
      next.index.toNat = valid.index.toNat + 1 → next.heap = valid.heap → tailCost ≤ middle.clock →
      let evaluated := evaluateHOLFiniteState middle continuation
      middle.clock ≤ evaluated.2.clock + tailCost ∧ evaluated.2.clock ≤ middle.clock ∧ evaluated.1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state (.seq transactionToField (.seq transactionIndexAdvance continuation))
    state.clock ≤ evaluated.2.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634 + tailCost) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  apply transaction_to_heap_continuation_bounded state array count tx kind input inputLength scratch frame ceiling inputLimit
    valid inside inputBound limitBound orderedFrame framePositive scratchBelow arrayFits arrayAbove
    headerBefore (.seq transactionIndexAdvance continuation) tailCost budget
  intro middle next indexEqual heapEqual ticks
  have nextInside : next.index.toNat < count.toNat := by rw [indexEqual]; exact inside
  apply transaction_index_heap_continuation_bounded middle array count tx kind input inputLength scratch frame ceiling next nextInside continuation tailCost
  intro output active advanced sameHeap sameClock
  have activeIndex : active.index.toNat = valid.index.toNat + 1 := by rw [indexEqual] at advanced; exact advanced
  have remaining := tailBound output active activeIndex (sameHeap.trans heapEqual) (by rw [sameClock]; exact ticks)
  exact remaining

#print axioms transaction_to_advance_heap_continuation_bounded
end InitECandidate.Runtime
