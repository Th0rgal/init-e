import InitECandidate.Runtime.TransactionWordHeapWitness
import InitECandidate.Runtime.TransactionGasSuffixBound
import InitECandidate.Runtime.TransactionGasAdvanceSuffixHeapKindBound
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_gas_suffix_heap_bounded_by_kind {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (fields : valid.index.toNat + (if kind = 0#64 then 0 else 1) + (if kind = 3#64 then 2 else 0) + (if kind = 4#64 then 1 else 0) + 7 ≤ count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 120 < 2^64)
    (arrayAbove : ceiling ≤ array.toNat)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (headerBefore : tx.toNat + 344 < array.toNat)
    (budget : transactionGasSuffixCost inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (transactionAt 23)
    state.clock ≤ evaluated.2.clock + transactionGasSuffixCost inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let first := inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92643
  let tail := transactionToSuffixCost inputLength.toNat
  have ticks : first + tail ≤ state.clock := budget
  have firstBudget : first ≤ state.clock := by omega
  have inside : valid.index.toNat < count.toNat := by omega
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) transactionGasArguments =
      some [.val (.word array),.val (.word valid.index),.val (.word (0 : BitVec 64)),.val (.word (14 : BitVec 64))] := by
    simp [transactionGasArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,valid.arrayLocal,valid.indexLocal]
  have bounded := evaluate_transaction_word_field_bounded state (ofString "w")
    (.op .add [.var .local (ofString "tx"),.const 144]) transactionGasArguments array valid.index 0 14 input inputLength scratch frame count.toNat ceiling inputLimit
    args valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code orderedFrame framePositive scratchBelow valid.arena firstBudget
  change state.clock ≤ (evaluateHOLFiniteState state (transactionWordField 144 transactionGasArguments)).2.clock + first ∧
    (evaluateHOLFiniteState state (transactionWordField 144 transactionGasArguments)).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState state (transactionWordField 144 transactionGasArguments)).1 ≠ some .timeOut at bounded
  rw [source_transaction_gas_suffix,← evaluate_seq_assoc]
  change state.clock ≤ (evaluateHOLFiniteState state (.seq (transactionWordField 144 transactionGasArguments) (transactionAt 25))).2.clock + transactionGasSuffixCost inputLength.toNat ∧
    (evaluateHOLFiniteState state (.seq (transactionWordField 144 transactionGasArguments) (transactionAt 25))).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState state (.seq (transactionWordField 144 transactionGasArguments) (transactionAt 25))).1 ≠ some .timeOut
  rw [evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState state (transactionWordField 144 transactionGasArguments) with
  | mk result middle =>
    rw [run] at bounded
    dsimp only at bounded ⊢
    cases result with
    | some result =>
      exact ⟨by dsimp [transactionGasSuffixCost,first] at *; omega,bounded.2.1,bounded.2.2⟩
    | none =>
      dsimp only
      obtain ⟨next,indexEqual,heapEqual⟩ := transaction_decode_heap_witness_after_word state middle array count tx kind input inputLength scratch frame ceiling inputLimit
        valid 144 0 14 transactionGasArguments args inside inputBound limitBound orderedFrame framePositive scratchBelow (by have h := valid.arrayBeforeHeap; omega) arrayAbove
        (by change tx.toNat + 144 < array.toNat; omega) firstBudget run
      have nextFields : next.index.toNat + (if kind = 0#64 then 0 else 1) + (if kind = 3#64 then 2 else 0) + (if kind = 4#64 then 1 else 0) + 7 ≤ count.toNat := by rw [indexEqual]; exact fields
      have futureTicks : tail ≤ middle.clock := by have spent := bounded.1; omega
      have remaining := transaction_gas_advance_suffix_heap_bounded_by_kind middle array count tx kind input inputLength scratch frame ceiling inputLimit
        next nextFields inputBound limitBound orderedFrame framePositive scratchBelow countLimit arrayAbove inputBeforeFrame headerBefore futureTicks
      exact ⟨by dsimp [transactionGasSuffixCost,first,tail] at *; omega,
        Nat.le_trans remaining.2.1 bounded.2.1,remaining.2.2⟩

#print axioms transaction_gas_suffix_heap_bounded_by_kind
end InitECandidate.Runtime
