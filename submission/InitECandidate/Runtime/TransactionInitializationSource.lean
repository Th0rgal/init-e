import InitECandidate.Runtime.TransactionInitializationLowerFrame
import InitECandidate.Runtime.TransactionMemzeroSuffixBound
import InitECandidate.Runtime.PanSeqAssoc
import InitECandidate.Runtime.TransactionDataScopedBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Grouping record initialization is an equality of the original evaluator,
including every exceptional and early result. -/
theorem evaluate_transaction_initialization_source {F : Type} (state : PanSemStateFiniteExact 64 F) :
    evaluateHOLFiniteState state (transactionAt 3) =
      evaluateHOLFiniteState state (.seq transactionRecordInitialization (transactionAt 6)) := by
  rw [source_transaction_memzero,source_transactionInputPointerStore,source_transactionInputLengthStore]
  unfold transactionRecordInitialization
  rw [evaluate_seq_assoc]
  apply evaluate_seq_second_congr
  intro current
  exact (evaluate_seq_assoc current transactionInputPointerStore transactionInputLengthStore (transactionAt 6)).symm

/-- Reaching the later decoder normally exposes an actual intermediate state
at the parsing stage; initialization cannot be skipped in the proof. -/
theorem transaction_initialization_normal_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState state (transactionAt 3) = (none,post)) :
    ∃ middle, evaluateHOLFiniteState state transactionRecordInitialization = (none,middle) ∧
      evaluateHOLFiniteState middle (transactionAt 6) = (none,post) := by
  rw [evaluate_transaction_initialization_source,evaluateHOLFiniteState_seq_line780] at run
  cases initialized : evaluateHOLFiniteState state transactionRecordInitialization with
  | mk result middle =>
    rw [initialized] at run
    cases result with
    | none => exact ⟨middle,rfl,run⟩
    | some result => cases run

theorem transaction_initialization_normal_input_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (tx input length array count wholeInput wholeLength : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word input)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (budget : 401 ≤ state.clock)
    (small : tx.toNat + 400 ≤ 33806089496) (aligned : tx.toNat % 8 = 0)
    (arena : ∀ address : BitVec 64, tx.toNat ≤ address.toNat → address.toNat < tx.toNat + 400 → state.memaddrs address)
    (valid : RlpSliceInputPrefix state array wholeInput wholeLength count.toNat)
    (before : array.toNat + count.toNat * 16 ≤ tx.toNat)
    (run : evaluateHOLFiniteState state (transactionAt 3) = (none,post)) :
    ∃ middle, evaluateHOLFiniteState state transactionRecordInitialization = (none,middle) ∧
      evaluateHOLFiniteState middle (transactionAt 6) = (none,post) ∧
      RlpSliceInputPrefix middle array wholeInput wholeLength count.toNat := by
  obtain ⟨middle,initialized,tail⟩ := transaction_initialization_normal_prefix state post run
  have retained := transaction_record_initialization_input_prefix state tx input length array count wholeInput wholeLength
    txLocal pointerLocal lengthLocal code budget small aligned arena valid before
  rw [initialized] at retained
  exact ⟨middle,initialized,tail,retained⟩

#print axioms transaction_initialization_normal_input_prefix
#print axioms evaluate_transaction_initialization_source
#print axioms transaction_initialization_normal_prefix
end InitECandidate.Runtime
