import InitECandidate.Runtime.TransactionU256HeapWitness
import InitECandidate.Runtime.TransactionU256FieldBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Compose a real scalar-field execution with a continuation using its retained heap witness. -/
theorem transaction_u256_heap_continuation_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (offset maximum : BitVec 64) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word array),.val (.word valid.index),.val (.word maximum)])
    (inside : valid.index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (headerBefore : tx.toNat + offset.toNat + 24 < array.toNat)
    (continuation : ProgHOL 64) (tailCost : Nat)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668 + tailCost ≤ state.clock)
    (tailBound : ∀ middle : PanSemStateFiniteExact 64 F,
      ∀ next : TransactionDecodeWitness middle array count tx kind input inputLength scratch frame ceiling,
      next.index = valid.index → next.heap = valid.heap → tailCost ≤ middle.clock →
      let evaluated := evaluateHOLFiniteState middle continuation
      middle.clock ≤ evaluated.2.clock + tailCost ∧ evaluated.2.clock ≤ middle.clock ∧ evaluated.1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state (.seq (transactionU256Field offset arguments) continuation)
    state.clock ≤ evaluated.2.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668 + tailCost) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have firstBudget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668 ≤ state.clock := by omega
  have first := evaluate_transaction_u256_field_bounded state (ofString "v")
    (.op .add [.var .local (ofString "tx"),.const offset]) arguments array valid.index maximum input inputLength scratch frame count.toNat ceiling inputLimit
    args valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code
    orderedFrame framePositive scratchBelow valid.arena firstBudget
  change state.clock ≤ (evaluateHOLFiniteState state (transactionU256Field offset arguments)).2.clock +
      (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ∧
    (evaluateHOLFiniteState state (transactionU256Field offset arguments)).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState state (transactionU256Field offset arguments)).1 ≠ some .timeOut at first
  rw [evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState state (transactionU256Field offset arguments) with
  | mk result middle =>
    rw [run] at first
    dsimp only at first ⊢
    cases result with
    | some result =>
      dsimp only
      exact ⟨by omega,first.2.1,first.2.2⟩
    | none =>
      dsimp only
      obtain ⟨next,indexEqual,heapEqual⟩ := transaction_decode_heap_witness_after_u256 state middle
        array count tx kind input inputLength scratch frame ceiling inputLimit valid offset maximum arguments args inside inputBound limitBound
        orderedFrame framePositive scratchBelow arrayFits arrayAbove headerBefore firstBudget run
      have ticks : tailCost ≤ middle.clock := by have spent := first.1; omega
      have tail := tailBound middle next indexEqual heapEqual ticks
      exact ⟨by omega,tail.2.1.trans first.2.1,tail.2.2⟩

#print axioms transaction_u256_heap_continuation_bounded
end InitECandidate.Runtime
