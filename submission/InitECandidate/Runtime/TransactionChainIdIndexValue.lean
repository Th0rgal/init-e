import InitECandidate.Runtime.TransactionChainIdSource
import InitECandidate.Runtime.LocalAssignNormalValue
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

private theorem finish_index {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
      obtain ⟨value,evaluated,updated⟩ := evaluate_local_assign_normal_value middle post (ofString "k") (.const 1) run
      have parsed : value = .val (.word (1 : BitVec 64)) := by simpa [evalHOLExact] using evaluated.symm
      rw [parsed] at updated
      rw [updated]
      simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

/-- Normal chain-ID processing consumes one field exactly for typed transactions. -/
theorem transaction_chain_id_normal_index {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (kind : BitVec 64)
    (typeLocal : state.locals.lookup (ofString "t") = some (.val (.word kind)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word 0)))
    (run : evaluateHOLFiniteState state transactionChainIdBranch = (none,post)) :
    post.locals.lookup (ofString "k") = some (.val (.word (if kind = 0 then 0 else 1))) := by
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notEqual (.var .local (ofString "t")) (.const 0)) =
      some (.val (.word (if kind = 0 then (0 : BitVec 64) else 1))) := by
    by_cases equal : kind = 0 <;> simp [evalHOLExact,typeLocal,Compiler.Encoders.Asm.wordCmpHOL,equal]
  unfold transactionChainIdBranch at run
  rw [evaluateHOLFiniteState_ite,condition] at run
  by_cases equal : kind = 0
  · rw [if_pos equal] at run ⊢
    dsimp only at run
    rw [evaluateHOLFiniteState_skip] at run
    cases run
    exact indexLocal
  · rw [if_neg equal] at run ⊢
    dsimp only at run
    rw [if_neg (by decide : (1 : BitVec 64) ≠ 0),evaluateHOLFiniteState_seq_line780] at run
    cases called : evaluateHOLFiniteState state
        (.call (some (some (.local,ofString "w"),none)) (ofString "tx_scalar_word") transactionChainIdArguments) with
    | mk result middle =>
      rw [called] at run
      cases result with
      | some result => cases run
      | none => exact finish_index middle post run

#print axioms transaction_chain_id_normal_index
end InitECandidate.Runtime
