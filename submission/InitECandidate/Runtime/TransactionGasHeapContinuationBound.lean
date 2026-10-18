import InitECandidate.Runtime.TransactionWordHeapContinuationBound
import InitECandidate.Runtime.TransactionIndexHeapContinuationBound
import InitECandidate.Runtime.TransactionGasSuffixBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_gas_heap_continuation_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (inside : valid.index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (headerBefore : tx.toNat + 144 < array.toNat)
    (continuation : ProgHOL 64) (tailCost : Nat)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92643 + tailCost ≤ state.clock)
    (tailBound : ∀ middle : PanSemStateFiniteExact 64 F,
      ∀ next : TransactionDecodeWitness middle array count tx kind input inputLength scratch frame ceiling,
      next.index.toNat = valid.index.toNat + 1 → next.heap = valid.heap → tailCost ≤ middle.clock →
      let evaluated := evaluateHOLFiniteState middle continuation
      middle.clock ≤ evaluated.2.clock + tailCost ∧ evaluated.2.clock ≤ middle.clock ∧ evaluated.1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state (.seq (transactionWordField 144 transactionGasArguments) (.seq transactionIndexAdvance continuation))
    state.clock ≤ evaluated.2.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92643 + tailCost) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) transactionGasArguments =
      some [.val (.word array),.val (.word valid.index),.val (.word (0 : BitVec 64)),.val (.word (14 : BitVec 64))] := by
    simp [transactionGasArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,valid.arrayLocal,valid.indexLocal]
  apply transaction_word_heap_continuation_bounded state array count tx kind input inputLength scratch frame ceiling inputLimit
    valid 144 0 14 transactionGasArguments args inside inputBound limitBound orderedFrame framePositive scratchBelow arrayFits arrayAbove
    headerBefore (.seq transactionIndexAdvance continuation) tailCost budget
  intro middle next indexEqual heapEqual ticks
  have nextInside : next.index.toNat < count.toNat := by rw [indexEqual]; exact inside
  apply transaction_index_heap_continuation_bounded middle array count tx kind input inputLength scratch frame ceiling next nextInside continuation tailCost
  intro output active advanced sameHeap sameClock
  have activeIndex : active.index.toNat = valid.index.toNat + 1 := by rw [indexEqual] at advanced; exact advanced
  have remaining := tailBound output active activeIndex (sameHeap.trans heapEqual) (by rw [sameClock]; exact ticks)
  exact remaining

#print axioms transaction_gas_heap_continuation_bounded
end InitECandidate.Runtime
