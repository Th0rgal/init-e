import InitECandidate.Runtime.TransactionU256HeapContinuationBound
import InitECandidate.Runtime.TransactionU256AtThenHeapBound
import InitECandidate.Runtime.TransactionFeeSuffixBound
import InitECandidate.Runtime.TransactionFeeLegacySuffixHeapKindBound
import InitECandidate.Runtime.TransactionFeeDynamicSuffixHeapKindBound
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_fee_suffix_heap_bounded_by_kind {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (fields : valid.index.toNat + (if kind = 0#64 then 0 else 1) + (if kind = 3#64 then 2 else 0) + (if kind = 4#64 then 1 else 0) + (if 1#64 < kind then 9 else 8) ≤ count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 120 < 2^64)
    (arrayAbove : ceiling ≤ array.toNat)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (headerBefore : tx.toNat + 344 < array.toNat)
    (budget : transactionFeeDynamicSuffixCost inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (transactionAt 22)
    state.clock ≤ evaluated.2.clock + transactionFeeDynamicSuffixCost inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  rw [source_transaction_fee]
  unfold transactionFeeBranch
  by_cases selected : 1#64 < kind
  · have condition : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .notLower (.const 1) (.var .local (ofString "t"))) = some (.val (.word (0 : BitVec 64))) := by
      simp [evalHOLExact,valid.typeLocal,Compiler.Encoders.Asm.wordCmpHOL,selected]
    have bounded := transaction_fee_dynamic_suffix_heap_bounded_by_kind state array count tx kind input inputLength scratch frame ceiling inputLimit
      valid (by simpa only [if_pos selected] using fields) inputBound limitBound orderedFrame framePositive scratchBelow countLimit arrayAbove inputBeforeFrame headerBefore budget
    rw [← evaluate_transaction_fee_dynamic_suffix] at bounded
    rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition]
    simpa only [ite_true,evaluateHOLFiniteState_seq_line780] using bounded
  · have condition : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .notLower (.const 1) (.var .local (ofString "t"))) = some (.val (.word (1 : BitVec 64))) := by
      simp [evalHOLExact,valid.typeLocal,Compiler.Encoders.Asm.wordCmpHOL,selected]
    have legacyBudget : transactionFeeLegacySuffixCost inputLength.toNat ≤ state.clock := by
      dsimp [transactionFeeLegacySuffixCost,transactionFeeDynamicSuffixCost] at *
      omega
    have bounded := transaction_fee_legacy_suffix_heap_bounded_by_kind state array count tx kind input inputLength scratch frame ceiling inputLimit
      valid (by simpa only [if_neg selected] using fields) inputBound limitBound orderedFrame framePositive scratchBelow countLimit arrayAbove inputBeforeFrame headerBefore legacyBudget
    rw [← evaluate_transaction_fee_legacy_suffix] at bounded
    have costLe : transactionFeeLegacySuffixCost inputLength.toNat ≤ transactionFeeDynamicSuffixCost inputLength.toNat := by
      dsimp [transactionFeeLegacySuffixCost,transactionFeeDynamicSuffixCost]; omega
    have enlarged : state.clock ≤ (evaluateHOLFiniteState state (.seq transactionFeeLegacy (transactionAt 23))).2.clock + transactionFeeDynamicSuffixCost inputLength.toNat ∧
        (evaluateHOLFiniteState state (.seq transactionFeeLegacy (transactionAt 23))).2.clock ≤ state.clock ∧
        (evaluateHOLFiniteState state (.seq transactionFeeLegacy (transactionAt 23))).1 ≠ some .timeOut :=
      ⟨Nat.le_trans bounded.1 (Nat.add_le_add_left costLe _),bounded.2⟩
    rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition]
    simpa only [show (1 : BitVec 64) ≠ 0 by decide,ite_false,evaluateHOLFiniteState_seq_line780] using enlarged

#print axioms transaction_fee_suffix_heap_bounded_by_kind
end InitECandidate.Runtime
