import InitECandidate.Runtime.TransactionDataSequenceBound
import InitECandidate.Runtime.TransactionTypedSignatureKindBound
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Isolated data-field sequencing supplies the combined cost before reattaching the enclosing source scope. -/
theorem transaction_data_sequence_bounded_by_kind {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (fields : valid.index.toNat + (if kind = 0#64 then 0 else 1) + (if kind = 3#64 then 2 else 0) + (if kind = 4#64 then 1 else 0) + 4 ≤ count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 120 < 2^64)
    (arrayBelow : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (headerBefore : tx.toNat + 344 < array.toNat)
    (reserve : valid.heap.toNat + inputLength.toNat * 40 + (inputLength.toNat * 48 + 46) * inputLength.toNat + inputLength.toNat * 296 + 7 ≤ frame.toNat)
    (budget : transactionDataSequenceCost inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state transactionDataSequence
    state.clock ≤ evaluated.2.clock + transactionDataSequenceCost inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let first := inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634
  let tail := transactionTypedSignatureCost inputLength.toNat
  have ticks : first + tail ≤ state.clock := budget
  have firstBudget : first ≤ state.clock := by omega
  have inside : valid.index.toNat < count.toNat := by omega
  have bounded := evaluate_transaction_data_field_bounded state array count valid.index input inputLength scratch frame ceiling inputLimit
    valid.arrayLocal valid.indexLocal valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code
    orderedFrame framePositive scratchBelow valid.arena firstBudget
  unfold transactionDataSequence
  rw [evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState state transactionDataField with
  | mk result middle =>
    rw [run] at bounded
    dsimp only at bounded ⊢
    cases result with
    | some result =>
      exact ⟨by dsimp [transactionDataSequenceCost,first] at *; omega,bounded.2.1,bounded.2.2⟩
    | none =>
      dsimp only
      obtain ⟨next,indexEqual,heapEqual,space,futureTicks⟩ := transaction_decode_after_data_reserves state middle
        array count tx kind input inputLength scratch frame ceiling inputLimit valid inside inputBound limitBound orderedFrame framePositive
        scratchBelow arrayBelow (by omega)
        (inputLength.toNat * 40 + (inputLength.toNat * 48 + 46) * inputLength.toNat + inputLength.toNat * 296 + 7) tail
        (by omega) ticks run
      have addOne : (valid.index + 1).toNat = valid.index.toNat + 1 := by
        rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change valid.index.toNat + 1 < 2^64; omega)]
        rfl
      have nextFields : next.index.toNat + (if kind = 0#64 then 0 else 1) + (if kind = 3#64 then 2 else 0) + (if kind = 4#64 then 1 else 0) + 3 ≤ count.toNat := by rw [indexEqual,addOne]; omega
      have remaining := transaction_typed_signature_bounded_by_kind middle array count tx kind input inputLength scratch frame ceiling inputLimit
        next nextFields inputBound limitBound orderedFrame framePositive scratchBelow countLimit arrayBelow headerBefore (by omega) futureTicks
      exact ⟨by dsimp [transactionDataSequenceCost,first,tail] at *; omega,
        Nat.le_trans remaining.2.1 bounded.2.1,remaining.2.2⟩

#print axioms transaction_data_sequence_bounded_by_kind
end InitECandidate.Runtime
