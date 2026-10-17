import InitECandidate.Runtime.ExtensionChildrenIn
import InitECandidate.Runtime.TrieWalkExtensionBranchChild
import InitECandidate.Runtime.TrieWalkExtensionReadFrame
import InitECandidate.Runtime.TrieWalkLoopRank
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A registered extension transition preserves the actual memory-based
registry, selects a live or null child, and decreases the exact loop rank.
The per-node zero-length order is derived from the constructor registry. -/
theorem evaluate_trieWalk_extension_registry_transition {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (live extensions : Set (BitVec 64))
    (node nibs index length : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (bounded : index.toNat ≤ length.toNat)
    (nodeNonzero : node ≠ 0) (member : node ∈ extensions)
    (order : ExtensionOrderFamily extensions state)
    (children : ExtensionChildrenIn live extensions state)
    (run : evaluateHOLFiniteState state trieWalkExtensionBranch = (none,post)) :
    ∃ child : BitVec 64, post.locals.lookup (ofString "node") = some (.val (.word child)) ∧
      (child = 0 ∨ child ∈ live) ∧
      trieWalkLoopRank length post < trieWalkLoopRank length state ∧
      ExtensionOrderFamily extensions post ∧ ExtensionChildrenIn live extensions post ∧
      post.memory = state.memory ∧ post.globals = state.globals := by
  obtain ⟨child,loaded,childLocal⟩ := evaluate_trieWalk_extension_branch_child state post node nibs index length
    nodeLocal nibsLocal posLocal nlenLocal code bounded run
  have liveChild := children node member child loaded
  have decrease := evaluate_trieWalk_extension_branch_rank_from_memory state post node nibs index length
    nodeLocal nibsLocal posLocal nlenLocal code bounded (order node member) run
  have rankDecrease := trieWalkLoopRank_decreases state post node child length nodeLocal childLocal nodeNonzero decrease
  have frame := evaluate_trieWalk_extension_branch_read_frame state node nibs index nodeLocal nibsLocal posLocal code
  rw [run] at frame
  dsimp only at frame
  refine ⟨child,childLocal,liveChild,rankDecrease,?_,?_,frame.1,frame.2⟩
  · intro old oldMember next empty nextLoaded
    rw [frame.1] at empty nextLoaded
    exact order old oldMember next empty nextLoaded
  · intro old oldMember next nextLoaded
    rw [frame.1] at nextLoaded
    exact children old oldMember next nextLoaded

#print axioms evaluate_trieWalk_extension_registry_transition
end InitECandidate.Runtime
