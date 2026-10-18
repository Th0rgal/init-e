import InitECandidate.Runtime.TransactionChainIdSource
import InitECandidate.Runtime.LocalAssignNormalValue
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_chain_id_finish_index {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState state transactionChainIdFinish = (none,post)) :
    post.locals.lookup (ofString "k") = some (.val (.word (1 : BitVec 64))) := by
  unfold transactionChainIdFinish at run
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases stored : evaluateHOLFiniteState state
      (.store (.op .add [.var .local (ofString "tx"),.const 8]) (.var .local (ofString "w"))) with
  | mk result middle =>
    rw [stored] at run
    cases result with
    | some result => cases run
    | none =>
      dsimp only at run
      obtain ⟨value,evaluated,updated⟩ := evaluate_local_assign_normal_value middle post (ofString "k") (.const 1) run
      have parsed : value = .val (.word (1 : BitVec 64)) := by
        simpa [evalHOLExact] using evaluated.symm
      rw [updated,parsed]
      simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

/-- The legacy path leaves the index alone; the typed path initializes it to one. -/
theorem transaction_chain_id_index {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (index : BitVec 64)
    (binding : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (run : evaluateHOLFiniteState state transactionChainIdBranch = (none,post)) :
    post.locals.lookup (ofString "k") = some (.val (.word index)) ∨
    post.locals.lookup (ofString "k") = some (.val (.word (1 : BitVec 64))) := by
  unfold transactionChainIdBranch at run
  rw [evaluateHOLFiniteState_ite] at run
  split at run
  · split at run
    · rw [evaluateHOLFiniteState_skip] at run
      cases run
      exact Or.inl binding
    · rw [evaluateHOLFiniteState_seq_line780] at run
      cases called : evaluateHOLFiniteState state
          (.call (some (some (.local,ofString "w"),none)) (ofString "tx_scalar_word") transactionChainIdArguments) with
      | mk result middle =>
        rw [called] at run
        cases result with
        | some result => cases run
        | none => exact Or.inr (transaction_chain_id_finish_index middle post run)
  · cases run

#print axioms transaction_chain_id_finish_index
#print axioms transaction_chain_id_index
end InitECandidate.Runtime
