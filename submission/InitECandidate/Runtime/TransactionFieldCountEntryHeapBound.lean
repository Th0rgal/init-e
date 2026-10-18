import InitECandidate.Runtime.TransactionFieldCountSource
import InitECandidate.Runtime.TransactionIndexEntryHeapBound
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_field_count_entry_heap_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count expected tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness (setVarHOLFinite (ofString "k") (.val (.word 0)) state) array count tx kind input inputLength scratch frame ceiling)
    (listLocal : state.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]))
    (expectedLocal : state.locals.lookup (ofString "nfields") = some (.val (.word expected)))
    (fields : (if kind = 0#64 then (0 : BitVec 64) else 1).toNat + (if kind = 0#64 then 0 else 1) + (if kind = 3#64 then 2 else 0) + (if kind = 4#64 then 1 else 0) + (if 1#64 < kind then 10 else 9) ≤ expected.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 120 < 2^64)
    (arrayAbove : ceiling ≤ array.toNat)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (headerBefore : tx.toNat + 344 < array.toNat)
    (budget : transactionChainIdSuffixCost inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (transactionAt 14)
    state.clock ≤ evaluated.2.clock + transactionChainIdSuffixCost inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notEqual (.rfield 1 (.var .local (ofString "lst"))) (.var .local (ofString "nfields"))) =
      some (.val (.word (if count = expected then (0 : BitVec 64) else 1))) := by
    by_cases equal : count = expected <;>
      simp [evalHOLExact,listLocal,expectedLocal,Compiler.Encoders.Asm.wordCmpHOL,equal]
  rw [source_transaction_field_count,evaluateHOLFiniteState_seq_line780]
  unfold transactionFieldCountGuard
  rw [evaluateHOLFiniteState_ite,condition]
  by_cases equal : count = expected
  · rw [if_pos equal]
    dsimp only
    rw [evaluateHOLFiniteState_skip]
    exact transaction_index_entry_heap_bounded state array count tx kind input inputLength scratch frame ceiling inputLimit
      valid (by rw [equal]; exact fields) inputBound limitBound orderedFrame framePositive scratchBelow countLimit arrayAbove inputBeforeFrame headerBefore budget
  · rw [if_neg equal]
    dsimp only
    rw [if_neg (by decide : (1 : BitVec 64) ≠ 0),evaluateHOLFiniteState_raise]
    simp only [evalHOLExact]
    cases shape : state.eshapes.lookup (ofString "TxErr") with
    | none => simp
    | some shape =>
      dsimp only
      split_ifs <;> dsimp only <;> exact ⟨by change state.clock ≤ state.clock + _; omega,Nat.le_refl _,by simp⟩

#print axioms transaction_field_count_entry_heap_bounded
end InitECandidate.Runtime
