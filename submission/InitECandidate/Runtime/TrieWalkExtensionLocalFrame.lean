import InitECandidate.Runtime.TrieWalkComparisonLocalFrame
import InitECandidate.Runtime.TrieWalkExtensionBranchRank
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal extension iterations preserve traversal locals such as nibs and
nlen through the length declaration, actual comparison and both restorations. -/
theorem evaluate_trieWalk_extension_branch_local_frame {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (node nibs index length : BitVec 64) (key : MlS)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word length)))
    (keyNode : key ≠ ofString "node") (keyPos : key ≠ ofString "pos")
    (keyResult : key ≠ ofString "eq2") (keyLength : key ≠ ofString "sl")
    (code : state.code = originalRuntimeCode) (bounded : index.toNat ≤ length.toNat)
    (run : evaluateHOLFiniteState state trieWalkExtensionBranch = (none,post)) :
    post.locals.lookup key = state.locals.lookup key := by
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
  have frame := evaluate_trieWalk_extension_comparison_local_frame entered output node nibs index size key
    ((kept _ (by decide)).trans nodeLocal) ((kept _ (by decide)).trans nibsLocal) atPos sizeLocal
    keyNode keyPos keyResult code comparison
  rw [restored]
  exact (saved_local_lookup_other output.locals (ofString "sl") key _ keyLength).trans
    (frame.trans (kept key keyLength))

#print axioms evaluate_trieWalk_extension_branch_local_frame
end InitECandidate.Runtime
