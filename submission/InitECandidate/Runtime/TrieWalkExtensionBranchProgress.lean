import InitECandidate.Runtime.TrieWalkExtensionGuardProgress
import InitECandidate.Runtime.PanDecNormalScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original extension-branch progress, including its memory load,
comparison call and restoration of both temporary locals. The segment length
is the actual pre-state memory word, not a supplied success witness. -/
theorem evaluate_trieWalk_extension_branch_progress {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (node nibs index length : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (bounded : index.toNat ≤ length.toNat)
    (run : evaluateHOLFiniteState state trieWalkExtensionBranch = (none,post)) :
    ∃ size : BitVec 64, state.memaddrs (node + BitVec.ofNat 64 40) ∧
      state.memory (node + BitVec.ofNat 64 40) = .word size ∧
      post.locals.lookup (ofString "pos") = some (.val (.word (index + size))) ∧
      post.locals.lookup (ofString "nlen") = some (.val (.word length)) ∧
      index.toNat + size.toNat ≤ length.toNat ∧
      (index + size).toNat ≤ length.toNat ∧
      trieWalkPositionRank length post ≤ trieWalkPositionRank length state ∧
      (trieWalkPositionRank length post < trieWalkPositionRank length state ↔ 0 < size.toNat) := by
  classical
  rw [source_trieWalk_extension_branch] at run
  obtain ⟨value,output,initialized,tail,restored⟩ := evaluate_dec_normal_scope state post (ofString "sl") .one
    (.load .one (.op .add [.var .local (ofString "node"),.const 40])) trieWalkExtensionAfterLength run
  by_cases accessible : state.memaddrs (node + BitVec.ofNat 64 40)
  · cases memory : state.memory (node + BitVec.ofNat 64 40) with
    | word size =>
      have actual : @evalHOLExact 64 F _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address))
          (.load .one (.op .add [.var .local (ofString "node"),.const 40])) = some (.val (.word size)) := by
        simp [evalHOLExact,evalListHOLExact,nodeLocal,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,accessible,memory]
      have valueEq := Option.some.inj (initialized.symm.trans actual)
      subst value
      let entered := setVarHOLFinite (ofString "sl") (.val (.word size)) state
      have kept : ∀ name, name ≠ ofString "sl" → entered.locals.lookup name = state.locals.lookup name := by
        intro name different
        simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
      have sizeLocal : entered.locals.lookup (ofString "sl") = some (.val (.word size)) := by
        simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      have enteredPos : entered.locals.lookup (ofString "pos") = some (.val (.word index)) := (kept _ (by decide)).trans posLocal
      obtain ⟨advanced,keptLength,postBound,_,_⟩ := evaluate_trieWalk_extension_guard_progress entered output node nibs index size length
        (by rw [kept _ (by decide)]; exact nodeLocal) (by rw [kept _ (by decide)]; exact nibsLocal)
        enteredPos sizeLocal (by rw [kept _ (by decide)]; exact nlenLocal) code bounded tail
      obtain ⟨within,_⟩ := evaluate_trieWalk_extension_guard_normal entered output index size length
        enteredPos sizeLocal ((kept _ (by decide)).trans nlenLocal) bounded tail
      have nextNat : (index + size).toNat = index.toNat + size.toNat := by
        rw [BitVec.toNat_add_of_lt (by have limit := length.isLt; change index.toNat + size.toNat < 2 ^ 64; omega)]
      have postPos : post.locals.lookup (ofString "pos") = some (.val (.word (index + size))) := by
        rw [restored]
        exact (saved_local_lookup_other output.locals (ofString "sl") (ofString "pos") _ (by decide)).trans advanced
      refine ⟨size,accessible,rfl,postPos,?_,within,postBound,?_,?_⟩
      · rw [restored]
        exact (saved_local_lookup_other output.locals (ofString "sl") (ofString "nlen") _ (by decide)).trans keptLength
      · simp only [trieWalkPositionRank,postPos,posLocal]
        rw [nextNat]
        omega
      · simp only [trieWalkPositionRank,postPos,posLocal]
        rw [nextNat]
        omega
  · have failed : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.load .one (.op .add [.var .local (ofString "node"),.const 40])) = none := by
      simp [evalHOLExact,evalListHOLExact,nodeLocal,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,accessible]
    rw [failed] at initialized
    cases initialized

#print axioms evaluate_trieWalk_extension_branch_progress
end InitECandidate.Runtime
