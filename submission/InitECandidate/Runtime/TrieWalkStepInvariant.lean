import InitECandidate.Runtime.TrieWalkStepRank
import InitECandidate.Runtime.TrieWalkExtensionLocalFrame
import InitECandidate.Runtime.TrieWalkExtensionReadFrame
import InitECandidate.Runtime.PanEvaluationMetadata
import InitECandidate.Runtime.TrieWalkBranchChild
import InitECandidate.Runtime.TrieWalkStepBound
import InitECandidate.Runtime.TrieWalkExtensionBranchChild
import InitECandidate.Runtime.TrieWalkLoopRank
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every normal original traversal iteration preserves typed traversal
locals, the key-position bound, original memory/globals and runtime code.
This theorem does not assume the zero-length child-order invariant. -/
theorem evaluate_trieWalk_step_invariant {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (node nibs index length : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (bounded : index.toNat ≤ length.toNat)
    (clockNonzero : state.clock ≠ 0)
    (run : evaluateHOLFiniteState state trieWalkStep = (none,post)) :
    ∃ child next : BitVec 64,
      post.locals.lookup (ofString "node") = some (.val (.word child)) ∧
      post.locals.lookup (ofString "pos") = some (.val (.word next)) ∧
      post.locals.lookup (ofString "nibs") = some (.val (.word nibs)) ∧
      post.locals.lookup (ofString "nlen") = some (.val (.word length)) ∧
      next.toNat ≤ length.toNat ∧ post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code := by
  classical
  have postCode : post.code = state.code := by
    have metadata := evaluateHOLFiniteState_metadata state trieWalkStep
    rw [run] at metadata
    exact metadata.1
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
      have normal : ∃ child next : BitVec 64,
          output.locals.lookup (ofString "node") = some (.val (.word child)) ∧
          output.locals.lookup (ofString "pos") = some (.val (.word next)) ∧
          output.locals.lookup (ofString "nibs") = some (.val (.word nibs)) ∧
          output.locals.lookup (ofString "nlen") = some (.val (.word length)) ∧
          next.toNat ≤ length.toNat ∧ output.memory = state.memory ∧ output.globals = state.globals := by
        rcases evaluate_trieWalk_after_kind_normal entered output kind kindLocal code clockNonzero tail with ⟨_,extension⟩ | ⟨_,_,_,branch⟩
        · obtain ⟨size,_,_,postPos,postLen,_,posBound,_,_⟩ := evaluate_trieWalk_extension_branch_progress
            entered output node nibs index length atNode atNibs atPos atLength code bounded extension
          obtain ⟨child,_,postNode⟩ := evaluate_trieWalk_extension_branch_child entered output node nibs index length atNode atNibs atPos atLength code bounded extension
          have postNibs := (evaluate_trieWalk_extension_branch_local_frame entered output node nibs index length (ofString "nibs")
            atNode atNibs atPos atLength (by decide) (by decide) (by decide) (by decide) code bounded extension).trans atNibs
          have frame := evaluate_trieWalk_extension_branch_read_frame entered node nibs index atNode atNibs atPos code
          rw [extension] at frame
          exact ⟨child,index+size,postNode,postPos,postNibs,postLen,posBound,frame.1,frame.2⟩
        · obtain ⟨postPos,postLen,posBound,_,memory,globals,_⟩ := evaluate_trieWalk_branch_progress entered output index length atPos atLength bounded branch
          obtain ⟨child,postNode⟩ := evaluate_trieWalk_branch_child entered output branch
          have frame := (evaluate_trieWalk_branch_normal_position entered output index atPos branch).2.1
          have postNibs := (frame (ofString "nibs") (by decide) (by decide)).trans atNibs
          exact ⟨child,index+1,postNode,postPos,postNibs,postLen,posBound,memory,globals⟩
      obtain ⟨child,next,postNode,postPos,postNibs,postLen,nextBound,memory,globals⟩ := normal
      refine ⟨child,next,?_,?_,?_,?_,nextBound,?_,?_,postCode⟩
      · rw [restored]
        exact (saved_local_lookup_other output.locals (ofString "k") (ofString "node") _ (by decide)).trans postNode
      · rw [restored]
        exact (saved_local_lookup_other output.locals (ofString "k") (ofString "pos") _ (by decide)).trans postPos
      · rw [restored]
        exact (saved_local_lookup_other output.locals (ofString "k") (ofString "nibs") _ (by decide)).trans postNibs
      · rw [restored]
        exact (saved_local_lookup_other output.locals (ofString "k") (ofString "nlen") _ (by decide)).trans postLen
      · rw [restored]; exact memory
      · rw [restored]; exact globals
  · have failed : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.load .one (.op .add [.var .local (ofString "node"),.const 0])) = none := by
      simp [evalHOLExact,evalListHOLExact,nodeLocal,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,accessible]
    rw [failed] at initialized
    cases initialized

#print axioms evaluate_trieWalk_step_invariant
end InitECandidate.Runtime
