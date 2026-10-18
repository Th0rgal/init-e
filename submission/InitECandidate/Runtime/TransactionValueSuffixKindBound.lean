import InitECandidate.Runtime.TransactionValueSuffixBound
import InitECandidate.Runtime.TransactionValueAdvanceSuffixKindBound
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_value_suffix_bounded_by_kind {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (fields : valid.index.toNat + (if kind = 0#64 then 0 else 1) + (if kind = 3#64 then 2 else 0) + (if kind = 4#64 then 1 else 0) + 5 ≤ count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 120 < 2^64)
    (arrayBelow : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (headerBefore : tx.toNat + 344 < array.toNat)
    (reserve : valid.heap.toNat + inputLength.toNat * 40 + (inputLength.toNat * 48 + 46) * inputLength.toNat + inputLength.toNat * 296 + 7 ≤ frame.toNat)
    (budget : transactionValueSuffixCost inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (transactionAt 29)
    state.clock ≤ evaluated.2.clock + transactionValueSuffixCost inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let first := inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668
  let tail := transactionDataSequenceCost inputLength.toNat
  have ticks : first + tail ≤ state.clock := budget
  have firstBudget : first ≤ state.clock := by omega
  have inside : valid.index.toNat < count.toNat := by omega
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) transactionValueArguments =
      some [.val (.word array),.val (.word valid.index),.val (.word (32 : BitVec 64))] := by
    simp [transactionValueArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,valid.arrayLocal,valid.indexLocal]
  have bounded := evaluate_transaction_u256_field_bounded state (ofString "v")
    (.op .add [.var .local (ofString "tx"),.const 160]) transactionValueArguments array valid.index 32 input inputLength scratch frame count.toNat ceiling inputLimit
    args valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code orderedFrame framePositive scratchBelow valid.arena firstBudget
  change state.clock ≤ (evaluateHOLFiniteState state (transactionU256Field 160 transactionValueArguments)).2.clock + first ∧
    (evaluateHOLFiniteState state (transactionU256Field 160 transactionValueArguments)).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState state (transactionU256Field 160 transactionValueArguments)).1 ≠ some .timeOut at bounded
  rw [source_transaction_value_suffix,← evaluate_seq_assoc]
  change state.clock ≤ (evaluateHOLFiniteState state (.seq (transactionU256Field 160 transactionValueArguments) (transactionAt 31))).2.clock + transactionValueSuffixCost inputLength.toNat ∧
    (evaluateHOLFiniteState state (.seq (transactionU256Field 160 transactionValueArguments) (transactionAt 31))).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState state (.seq (transactionU256Field 160 transactionValueArguments) (transactionAt 31))).1 ≠ some .timeOut
  rw [evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState state (transactionU256Field 160 transactionValueArguments) with
  | mk result middle =>
    rw [run] at bounded
    dsimp only at bounded ⊢
    cases result with
    | some result =>
      exact ⟨by dsimp [transactionValueSuffixCost,first] at *; omega,bounded.2.1,bounded.2.2⟩
    | none =>
      dsimp only
      obtain ⟨next,indexEqual,heapEqual⟩ := transaction_decode_witness_after_u256 state middle array count tx kind input inputLength scratch frame ceiling inputLimit
        valid 160 32 transactionValueArguments args inside inputBound limitBound orderedFrame framePositive scratchBelow arrayBelow
        (by change tx.toNat + 160 + 24 < array.toNat; omega) firstBudget run
      have nextFields : next.index.toNat + (if kind = 0#64 then 0 else 1) + (if kind = 3#64 then 2 else 0) + (if kind = 4#64 then 1 else 0) + 5 ≤ count.toNat := by rw [indexEqual]; exact fields
      have futureTicks : tail ≤ middle.clock := by have spent := bounded.1; omega
      have remaining := transaction_value_advance_suffix_bounded_by_kind middle array count tx kind input inputLength scratch frame ceiling inputLimit
        next nextFields inputBound limitBound orderedFrame framePositive scratchBelow countLimit arrayBelow headerBefore (by rw [heapEqual]; exact reserve) futureTicks
      exact ⟨by dsimp [transactionValueSuffixCost,first,tail] at *; omega,
        Nat.le_trans remaining.2.1 bounded.2.1,remaining.2.2⟩

#print axioms transaction_value_suffix_bounded_by_kind
end InitECandidate.Runtime
