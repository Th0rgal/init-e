import InitECandidate.Runtime.TrieWalkStepRank
import InitECandidate.Runtime.ExtensionChildrenIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual source kind dispatch requires zero-length child ordering only for
registered extension nodes. Branch child slots need no address ordering. -/
theorem evaluate_trieWalk_step_registry_rank {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (node nibs index length : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (bounded : index.toNat ≤ length.toNat)
    (nodeNonzero : node ≠ 0) (clockNonzero : state.clock ≠ 0)
    (extensions : Set (BitVec 64)) (order : ExtensionOrderFamily extensions state)
    (classified : state.memory node = .word 2 → node ∈ extensions)
    (run : evaluateHOLFiniteState state trieWalkStep = (none,post)) :
    trieWalkLoopRank length post < trieWalkLoopRank length state := by
  classical
  rw [source_trieWalk_step_body] at run
  obtain ⟨value,output,initialized,tail,restored⟩ := evaluate_dec_normal_scope state post (ofString "k") .one
    (.load .one (.op .add [.var .local (ofString "node"),.const 0])) trieWalkAfterKind run
  by_cases accessible : state.memaddrs node
  · cases memory : state.memory node with
    | word kind =>
      have actual : @evalHOLExact 64 F _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address))
          (.load .one (.op .add [.var .local (ofString "node"),.const 0])) = some (.val (.word kind)) := by
        simp [evalHOLExact,evalListHOLExact,nodeLocal,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,accessible,memory]
      have valueEq := Option.some.inj (initialized.symm.trans actual)
      subst value
      let entered := setVarHOLFinite (ofString "k") (.val (.word kind)) state
      have kept : ∀ name, name ≠ ofString "k" → entered.locals.lookup name = state.locals.lookup name := by
        intro name different
        simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
      have kindLocal : entered.locals.lookup (ofString "k") = some (.val (.word kind)) := by
        simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      have atNode := (kept (ofString "node") (by decide)).trans nodeLocal
      have atPos := (kept (ofString "pos") (by decide)).trans posLocal
      have atNibs := (kept (ofString "nibs") (by decide)).trans nibsLocal
      have atLength := (kept (ofString "nlen") (by decide)).trans nlenLocal
      have enteredRank : trieWalkLoopRank length entered = trieWalkLoopRank length state :=
        trieWalkLoopRank_local_frame entered state length (kept _ (by decide)) (kept _ (by decide))
      have postRank : trieWalkLoopRank length post = trieWalkLoopRank length output := by
        apply trieWalkLoopRank_local_frame
        · rw [restored]; exact saved_local_lookup_other output.locals (ofString "k") (ofString "node") _ (by decide)
        · rw [restored]; exact saved_local_lookup_other output.locals (ofString "k") (ofString "pos") _ (by decide)
      have decreasing : trieWalkLoopRank length output < trieWalkLoopRank length entered := by
        rcases evaluate_trieWalk_after_kind_normal entered output kind kindLocal code clockNonzero tail with ⟨isExtension,extension⟩ | ⟨_,_,_,branch⟩
        · have registered : node ∈ extensions := classified (by simpa [isExtension] using memory)
          have emptyChildOrder := order node registered
          obtain ⟨child,_,childLocal⟩ := evaluate_trieWalk_extension_branch_child entered output node nibs index length atNode atNibs atPos atLength code bounded extension
          have decrease := evaluate_trieWalk_extension_branch_rank_from_memory entered output node nibs index length atNode atNibs atPos atLength code bounded emptyChildOrder extension
          exact trieWalkLoopRank_decreases entered output node child length atNode childLocal nodeNonzero decrease
        · obtain ⟨child,childLocal⟩ := evaluate_trieWalk_branch_child entered output branch
          have decrease := evaluate_trieWalk_branch_traversal_rank entered output index length node child atPos atLength atNode childLocal bounded branch
          exact trieWalkLoopRank_decreases entered output node child length atNode childLocal nodeNonzero decrease
      rw [postRank,← enteredRank]
      exact decreasing
  · have failed : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.load .one (.op .add [.var .local (ofString "node"),.const 0])) = none := by
      simp [evalHOLExact,evalListHOLExact,nodeLocal,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,accessible]
    rw [failed] at initialized
    cases initialized

#print axioms evaluate_trieWalk_step_registry_rank
end InitECandidate.Runtime
