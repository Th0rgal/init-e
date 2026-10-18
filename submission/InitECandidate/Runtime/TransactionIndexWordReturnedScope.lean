import InitECandidate.Runtime.TransactionIndexScopeBound
import InitECandidate.Runtime.PanDecReturnedScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual index and temporary-word declarations consume no clock and only
extend locals before chain-ID processing. Their final restoration affects no memory. -/
theorem transaction_index_word_returned_scope {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (transactionAt 15) = (some (.returned value),post)) :
    ∃ output : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState
        (setVarHOLFinite (ofString "w") (.val (.word 0))
          (setVarHOLFinite (ofString "k") (.val (.word 0)) state))
        (transactionAt 17) = (some (.returned value),output) ∧ post.memory = output.memory := by
  rw [source_transaction_index_scope] at run
  obtain ⟨index,indexOutput,indexInit,indexRun,indexScope⟩ := evaluate_dec_returned_scope state post
    (ofString "k") .one (.const 0) (transactionAt 16) value run
  have indexZero : index = .val (.word 0) := by simpa [evalHOLExact] using indexInit.symm
  subst index
  rw [source_transaction_word_scope] at indexRun
  obtain ⟨word,output,wordInit,bodyRun,wordScope⟩ := evaluate_dec_returned_scope
    (setVarHOLFinite (ofString "k") (.val (.word 0)) state) indexOutput
    (ofString "w") .one (.const 0) (transactionAt 17) value indexRun
  have wordZero : word = .val (.word 0) := by simpa [evalHOLExact] using wordInit.symm
  subst word
  exact ⟨output,bodyRun,by rw [indexScope,wordScope]⟩

#print axioms transaction_index_word_returned_scope
end InitECandidate.Runtime
