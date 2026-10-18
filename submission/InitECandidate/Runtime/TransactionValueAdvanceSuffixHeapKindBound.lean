import InitECandidate.Runtime.TransactionU256HeapWitness
import InitECandidate.Runtime.TransactionValueAdvanceSuffixBound
import InitECandidate.Runtime.TransactionDataScopedHeapKindBound
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_value_advance_suffix_heap_bounded_by_kind {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (fields : valid.index.toNat + (if kind = 0#64 then 0 else 1) + (if kind = 3#64 then 2 else 0) + (if kind = 4#64 then 1 else 0) + 5 ≤ count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 120 < 2^64)
    (arrayAbove : ceiling ≤ array.toNat)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (headerBefore : tx.toNat + 344 < array.toNat)
    (budget : transactionDataSequenceCost inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (transactionAt 31)
    state.clock ≤ evaluated.2.clock + transactionDataSequenceCost inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have inside : valid.index.toNat < count.toNat := by omega
  let next := valid.advanceIndex inside
  have addOne : (valid.index + 1).toNat = valid.index.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change valid.index.toNat + 1 < 2^64; omega)]
    rfl
  have nextFields : next.index.toNat + (if kind = 0#64 then 0 else 1) + (if kind = 3#64 then 2 else 0) + (if kind = 4#64 then 1 else 0) + 4 ≤ count.toNat := by
    change (valid.index + 1).toNat + (if kind = 0#64 then 0 else 1) + (if kind = 3#64 then 2 else 0) + (if kind = 4#64 then 1 else 0) + 4 ≤ count.toNat
    rw [addOne]; omega
  have bounded := transaction_data_scoped_heap_bounded_by_kind _ array count tx kind input inputLength scratch frame ceiling inputLimit
    next nextFields inputBound limitBound orderedFrame framePositive scratchBelow countLimit arrayAbove inputBeforeFrame headerBefore budget
  rw [source_transaction_value_advance,evaluateHOLFiniteState_seq_line780,transaction_index_advance_run state valid.index valid.indexLocal]
  dsimp only
  rw [evaluate_transaction_data_scope]
  exact bounded

#print axioms transaction_value_advance_suffix_heap_bounded_by_kind
end InitECandidate.Runtime
