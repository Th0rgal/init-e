import InitECandidate.Runtime.TransactionNonceReturnedScope
import InitECandidate.Runtime.TransactionNonceScopeBound
import InitECandidate.Runtime.PanDecReturnedScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful decoder continuation exposes the original nonce temporary scope. -/
theorem transaction_nonce_returned_scope_state {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (transactionAt 18) = (some (.returned value),post)) :
    ∃ output : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState (setVarHOLFinite (ofString "v") transactionNonceInitialValue state)
        (transactionAt 19) = (some (.returned value),output) ∧ (post.memory = output.memory ∧ post.globals = output.globals) := by
  rw [source_transaction_nonce_scope] at run
  obtain ⟨initial,output,initialized,tail,scope⟩ := evaluate_dec_returned_scope state post (ofString "v")
    (.comb [.one,.one,.one,.one]) (.rstruct [.const 0,.const 0,.const 0,.const 0]) (transactionAt 19) value run
  have actual : initial = transactionNonceInitialValue := by
    simpa [evalHOLExact,evalListHOLExact,transactionNonceInitialValue] using initialized.symm
  subst initial
  exact ⟨output,tail,by rw [scope]; exact ⟨rfl,rfl⟩⟩

#print axioms transaction_nonce_returned_scope_state
end InitECandidate.Runtime
