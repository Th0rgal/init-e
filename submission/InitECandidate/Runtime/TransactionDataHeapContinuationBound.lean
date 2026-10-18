import InitECandidate.Runtime.TransactionDataHeapClockReserve
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Compose the real data-field execution with a continuation using its retained heap witness. -/
theorem transaction_data_heap_continuation_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (inside : valid.index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (headerBefore : tx.toNat + 200 < array.toNat)
    (continuation : ProgHOL 64) (tailCost : Nat)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634 + tailCost ≤ state.clock)
    (tailBound : ∀ middle : PanSemStateFiniteExact 64 F,
      ∀ next : TransactionDecodeWitness middle array count tx kind input inputLength scratch frame ceiling,
      next.index = valid.index + 1 → next.heap = valid.heap → tailCost ≤ middle.clock →
      let evaluated := evaluateHOLFiniteState middle continuation
      middle.clock ≤ evaluated.2.clock + tailCost ∧ evaluated.2.clock ≤ middle.clock ∧ evaluated.1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state (.seq transactionDataField continuation)
    state.clock ≤ evaluated.2.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634 + tailCost) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have firstBudget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634 ≤ state.clock := by omega
  have first := evaluate_transaction_data_field_bounded state array count valid.index input inputLength scratch frame ceiling inputLimit
    valid.arrayLocal valid.indexLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code
    orderedFrame framePositive scratchBelow valid.arena firstBudget
  rw [evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState state transactionDataField with
  | mk result middle =>
    rw [run] at first
    dsimp only at first ⊢
    cases result with
    | some result =>
      dsimp only
      exact ⟨by omega,first.2.1,first.2.2⟩
    | none =>
      dsimp only
      obtain ⟨next,indexEqual,heapEqual,ticks⟩ := transaction_decode_after_data_heap_clock_reserve state middle
        array count tx kind input inputLength scratch frame ceiling inputLimit valid inside inputBound limitBound
        orderedFrame framePositive scratchBelow arrayFits arrayAbove headerBefore tailCost budget run
      have tail := tailBound middle next indexEqual heapEqual ticks
      exact ⟨by omega,tail.2.1.trans first.2.1,tail.2.2⟩

#print axioms transaction_data_heap_continuation_bounded
end InitECandidate.Runtime
