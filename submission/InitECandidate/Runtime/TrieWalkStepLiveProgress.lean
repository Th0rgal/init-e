import InitECandidate.Runtime.TrieWalkStepRank
import InitECandidate.Runtime.TrieWalkExtensionRegistryTransition
import InitECandidate.Runtime.TrieWalkBranchRegistryTransition
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every normal original iteration selects a live/null child and decreases
the loop rank using kind classification and memory-based child registries. -/
theorem evaluate_trieWalk_step_live_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (node nibs index length : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (bounded : index.toNat ≤ length.toNat)
    (nodeNonzero : node ≠ 0) (clockNonzero : state.clock ≠ 0)
    (live extensions branches : Set (BitVec 64)) (order : ExtensionOrderFamily extensions state)
    (classified : state.memory node = .word 2 → node ∈ extensions)
    (extensionChildren : ExtensionChildrenIn live extensions state)
    (branchChildren : BranchChildrenIn live branches state)
    (branchClassified : ∀ kind : BitVec 64, state.memory node = .word kind →
      kind ≠ 0 → kind ≠ 1 → kind ≠ 2 → node ∈ branches)
    (nibbles : TrieNibbleRange state nibs length)
    (run : evaluateHOLFiniteState state trieWalkStep = (none,post)) :
    ∃ child : BitVec 64, post.locals.lookup (ofString "node") = some (.val (.word child)) ∧
      (child = 0 ∨ child ∈ live) ∧ trieWalkLoopRank length post < trieWalkLoopRank length state := by
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
      have progress : ∃ child : BitVec 64,
          output.locals.lookup (ofString "node") = some (.val (.word child)) ∧
          (child = 0 ∨ child ∈ live) ∧ trieWalkLoopRank length output < trieWalkLoopRank length entered := by
        rcases evaluate_trieWalk_after_kind_normal entered output kind kindLocal code clockNonzero tail with
          ⟨isExtension,extension⟩ | ⟨notZero,notLeaf,notExtension,branch⟩
        · have registered : node ∈ extensions := classified (by simpa [isExtension] using memory)
          obtain ⟨child,atChild,liveChild,decrease,_⟩ := evaluate_trieWalk_extension_registry_transition
            entered output live extensions node nibs index length atNode atNibs atPos atLength code bounded
            nodeNonzero registered order extensionChildren extension
          exact ⟨child,atChild,liveChild,decrease⟩
        · have registered : node ∈ branches := branchClassified kind memory notZero notLeaf notExtension
          obtain ⟨child,atChild,liveChild,decrease,_⟩ := evaluate_trieWalk_branch_registry_transition
            entered output live branches node nibs index length atNode atNibs atPos atLength bounded
            nodeNonzero registered branchChildren (nibbles.after_frame rfl rfl rfl) branch
          exact ⟨child,atChild,liveChild,decrease⟩
      obtain ⟨child,atChild,liveChild,decrease⟩ := progress
      refine ⟨child,?_,liveChild,?_⟩
      · rw [restored,saved_local_lookup_other _ _ _ _ (by decide)]
        exact atChild
      · rw [postRank,← enteredRank]
        exact decrease
  · have failed : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.load .one (.op .add [.var .local (ofString "node"),.const 0])) = none := by
      simp [evalHOLExact,evalListHOLExact,nodeLocal,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,accessible]
    rw [failed] at initialized
    cases initialized

#print axioms evaluate_trieWalk_step_live_progress
end InitECandidate.Runtime
