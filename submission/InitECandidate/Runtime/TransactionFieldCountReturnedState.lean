import InitECandidate.Runtime.TransactionFieldCountSource
import InitECandidate.Runtime.TransactionArrayScopeBound
import InitECandidate.Runtime.TransactionTypeHeaderReturnedPrefix
import InitECandidate.Runtime.PanDecReturnedScope
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned decoder cannot have taken the field-count rejection branch. -/
theorem transaction_field_count_returned_state {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count expected : BitVec 64) (value : ValueHOL 64)
    (listLocal : state.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]))
    (expectedLocal : state.locals.lookup (ofString "nfields") = some (.val (.word expected)))
    (run : evaluateHOLFiniteState state (transactionAt 14) = (some (.returned value),post)) :
    count = expected ∧ evaluateHOLFiniteState state (transactionAt 15) = (some (.returned value),post) := by
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notEqual (.rfield 1 (.var .local (ofString "lst"))) (.var .local (ofString "nfields"))) =
      some (.val (.word (if count = expected then (0 : BitVec 64) else 1))) := by
    by_cases equal : count = expected <;>
      simp [evalHOLExact,listLocal,expectedLocal,Compiler.Encoders.Asm.wordCmpHOL,equal]
  rw [source_transaction_field_count,evaluateHOLFiniteState_seq_line780] at run
  unfold transactionFieldCountGuard at run
  rw [evaluateHOLFiniteState_ite,condition] at run
  by_cases equal : count = expected
  · rw [if_pos equal] at run
    dsimp only at run
    rw [evaluateHOLFiniteState_skip] at run
    exact ⟨equal,run⟩
  · rw [if_neg equal] at run
    dsimp only at run
    rw [if_neg (by decide : (1 : BitVec 64) ≠ 0)] at run
    have terminal := evaluate_raise_terminal state (ofString "TxErr") (.const 4)
    have noReturn := evaluate_raise_no_return state (ofString "TxErr") (.const 4) value
    cases raised : evaluateHOLFiniteState state (.raise (ofString "TxErr") (.const 4)) with
    | mk result middle =>
      rw [raised] at run terminal noReturn
      cases result with
      | none => exact False.elim (terminal rfl)
      | some result => exact False.elim (noReturn (Prod.mk.inj run).1)

/-- The actual array scope and field-count check expose the index declaration,
with the exact required count and unchanged memory, globals and clock. -/
theorem transaction_array_returned_field_count_state {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count expected : BitVec 64) (value : ValueHOL 64)
    (listLocal : state.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]))
    (expectedLocal : state.locals.lookup (ofString "nfields") = some (.val (.word expected)))
    (run : evaluateHOLFiniteState state (transactionAt 13) = (some (.returned value),post)) :
    count = expected ∧ ∃ output : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState (setVarHOLFinite (ofString "arr") (.val (.word array)) state)
        (transactionAt 15) = (some (.returned value),output) ∧ (post.memory = output.memory ∧ post.globals = output.globals) := by
  rw [source_transaction_array_scope] at run
  obtain ⟨initial,output,initialized,tail,scope⟩ := evaluate_dec_returned_scope state post (ofString "arr") .one
    (.rfield 0 (.var .local (ofString "lst"))) (transactionAt 14) value run
  have initialValue : initial = .val (.word array) := by
    simpa [evalHOLExact,listLocal] using initialized.symm
  subst initial
  have checked := transaction_field_count_returned_state (setVarHOLFinite (ofString "arr") (.val (.word array)) state)
    output array count expected value
    (by simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "arr" ≠ ofString "lst" by decide] using listLocal)
    (by simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "arr" ≠ ofString "nfields" by decide] using expectedLocal) tail
  exact ⟨checked.1,output,checked.2,by rw [scope]; exact ⟨rfl,rfl⟩⟩

#print axioms transaction_field_count_returned_state
#print axioms transaction_array_returned_field_count_state
end InitECandidate.Runtime
