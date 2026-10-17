import InitECandidate.Runtime.TrieWalkBranchAdvance
import InitECandidate.Runtime.LocalAssignNormalValue
import InitECandidate.Runtime.LoadOneWord
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_trieWalk_branch_node_load : ∃ address : ExpHOL 64, trieWalkBranchNodeExpression = .load .one address := by
  simp only [trieWalkBranchNodeExpression,trieWalkBranchAdvance,trieWalkBranchBranch,trieWalkStep,trieWalkLoop,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  exact ⟨_,rfl⟩

/-- A normally selected branch child has an actual word-valued node local.
The pointer is derived from the checked load and both local assignments. -/
theorem evaluate_trieWalk_branch_advance_child {F : Type}
    (state post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState state trieWalkBranchAdvance = (none,post)) :
    ∃ child : BitVec 64, post.locals.lookup (ofString "node") = some (.val (.word child)) := by
  rw [source_trieWalk_branch_advance,evaluateHOLFiniteState_seq_line780] at run
  cases assigned : evaluateHOLFiniteState state (.assign .local (ofString "node") trieWalkBranchNodeExpression) with
  | mk result middle =>
    rw [assigned] at run
    cases result with
    | none =>
      obtain ⟨value,evaluated,selected⟩ := evaluate_local_assign_normal_value state middle (ofString "node") trieWalkBranchNodeExpression assigned
      obtain ⟨address,source⟩ := source_trieWalk_branch_node_load
      rw [source] at evaluated
      obtain ⟨child,word⟩ := eval_load_one_word state address value evaluated
      change evaluateHOLFiniteState middle (.assign .local (ofString "pos") (.op .add [.var .local (ofString "pos"),.const 1])) = (none,post) at run
      obtain ⟨nextValue,_,advanced⟩ := evaluate_local_assign_normal_value middle post (ofString "pos") _ run
      refine ⟨child,?_⟩
      rw [advanced,selected,word]
      simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "pos" ≠ ofString "node" from by decide]
    | some result => cases run

theorem evaluate_trieWalk_branch_child {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState state trieWalkBranchBranch = (none,post)) :
    ∃ child : BitVec 64, post.locals.lookup (ofString "node") = some (.val (.word child)) :=
  evaluate_trieWalk_branch_advance_child state post (evaluate_trieWalk_branch_normal_advance state post run)

#print axioms source_trieWalk_branch_node_load
#print axioms evaluate_trieWalk_branch_advance_child
#print axioms evaluate_trieWalk_branch_child
end InitECandidate.Runtime
