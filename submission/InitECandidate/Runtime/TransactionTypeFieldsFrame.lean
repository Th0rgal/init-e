import InitECandidate.Runtime.TransactionTypeFields
import InitECandidate.Runtime.ReadOnlyMemory
import InitECandidate.Runtime.NamedGlobalFrame
import InitECandidate.Runtime.StraightLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Type-specific field-count selection changes only the nfields local. -/
theorem transaction_type_fields_frame {F : Type} (state : PanSemStateFiniteExact 64 F) :
    let output := evaluateHOLFiniteState state transactionTypeFields
    output.2.memory = state.memory ∧
    (∀ key, output.2.globals.lookup key = state.globals.lookup key) ∧
    (∀ key, key ≠ ofString "nfields" → output.2.locals.lookup key = state.locals.lookup key) := by
  refine ⟨evaluate_readOnly_memory transactionTypeFields (by rfl) state,?_,?_⟩
  · intro key
    exact evaluate_avoidsGlobalAssignment key transactionTypeFields (by rfl) state
  · intro key different
    apply evaluate_straight_local_frame key transactionTypeFields _ state
    simp [transactionTypeFields,transactionTypeFieldCase,straightLocalFrame,Ne.symm different]

/-- Every branch of the required-count formula fits in a source word. -/
theorem transaction_required_fields_word (kind : BitVec 64) :
    (BitVec.ofNat 64 (transactionRequiredFields kind)).toNat = transactionRequiredFields kind := by
  have bounded : transactionRequiredFields kind < 2^64 := by
    unfold transactionRequiredFields
    split_ifs <;> decide
  exact Nat.mod_eq_of_lt bounded

#print axioms transaction_type_fields_frame
#print axioms transaction_required_fields_word
end InitECandidate.Runtime
