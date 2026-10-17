import InitECandidate.Runtime.TrieWalkComparisonChild
import InitECandidate.Runtime.TrieWalkExtensionBranchRank
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original extension-branch child identity, including the length
load, guard, memeq call and both local restorations. -/
theorem evaluate_trieWalk_extension_branch_child {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (node nibs index length : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (bounded : index.toNat ≤ length.toNat)
    (run : evaluateHOLFiniteState state trieWalkExtensionBranch = (none,post)) :
    ∃ child : BitVec 64, state.memory (node + BitVec.ofNat 64 48) = .word child ∧
      post.locals.lookup (ofString "node") = some (.val (.word child)) := by
  obtain ⟨size,accessible,loaded,_,_,_,_,_,_⟩ := evaluate_trieWalk_extension_branch_progress
    state post node nibs index length nodeLocal nibsLocal posLocal nlenLocal code bounded run
  rw [source_trieWalk_extension_branch] at run
  obtain ⟨value,output,initialized,tail,restored⟩ := evaluate_dec_normal_scope state post (ofString "sl") .one
    (.load .one (.op .add [.var .local (ofString "node"),.const 40])) trieWalkExtensionAfterLength run
  have actual : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (.op .add [.var .local (ofString "node"),.const 40])) = some (.val (.word size)) := by
    simp [evalHOLExact,evalListHOLExact,nodeLocal,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,accessible,loaded]
  have valueEq := Option.some.inj (initialized.symm.trans actual)
  subst value
  let entered := setVarHOLFinite (ofString "sl") (.val (.word size)) state
  have kept : ∀ name, name ≠ ofString "sl" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have sizeLocal : entered.locals.lookup (ofString "sl") = some (.val (.word size)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atPos : entered.locals.lookup (ofString "pos") = some (.val (.word index)) := (kept _ (by decide)).trans posLocal
  obtain ⟨_,comparison⟩ := evaluate_trieWalk_extension_guard_normal entered output index size length atPos sizeLocal
    ((kept _ (by decide)).trans nlenLocal) bounded tail
  obtain ⟨child,memory,childLocal⟩ := evaluate_trieWalk_extension_comparison_child entered output node nibs index size
    ((kept _ (by decide)).trans nodeLocal) ((kept _ (by decide)).trans nibsLocal) atPos sizeLocal code comparison
  refine ⟨child,memory,?_⟩
  rw [restored]
  exact (saved_local_lookup_other output.locals (ofString "sl") (ofString "node") _ (by decide)).trans childLocal

/-- Full extension-rank decrease from a pre-state memory ordering property.
The selected child is derived from source evaluation, not assumed as a final
local binding. Establishing this ordering for constructed nodes remains a
separate trie invariant obligation. -/
theorem evaluate_trieWalk_extension_branch_rank_from_memory {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (node nibs index length : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (bounded : index.toNat ≤ length.toNat)
    (emptyChildOrder : ∀ child : BitVec 64,
      state.memory (node + BitVec.ofNat 64 40) = .word 0 →
      state.memory (node + BitVec.ofNat 64 48) = .word child → child.toNat < node.toNat)
    (run : evaluateHOLFiniteState state trieWalkExtensionBranch = (none,post)) :
    trieWalkTraversalRank length post < trieWalkTraversalRank length state := by
  obtain ⟨child,loaded,childLocal⟩ := evaluate_trieWalk_extension_branch_child state post node nibs index length
    nodeLocal nibsLocal posLocal nlenLocal code bounded run
  exact evaluate_trieWalk_extension_branch_rank state post node child nibs index length
    nodeLocal childLocal nibsLocal posLocal nlenLocal code bounded
    (fun empty => emptyChildOrder child empty loaded) run

#print axioms evaluate_trieWalk_extension_branch_rank_from_memory
#print axioms evaluate_trieWalk_extension_branch_child
end InitECandidate.Runtime
