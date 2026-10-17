import InitECandidate.Runtime.BranchChildrenIn
import InitECandidate.Runtime.TrieWalkLoopRank
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A normal registered branch transition selects a live/null child using
its actual readable nibble, preserves the buffer and registry, and decreases
the exact loop rank. Nibble range remains an explicit buffer invariant. -/
theorem evaluate_trieWalk_branch_registry_transition {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (live branches : Set (BitVec 64))
    (node nibs index length : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word length)))
    (bounded : index.toNat ≤ length.toNat) (nodeNonzero : node ≠ 0) (member : node ∈ branches)
    (children : BranchChildrenIn live branches state) (nibbles : TrieNibbleRange state nibs length)
    (run : evaluateHOLFiniteState state trieWalkBranchBranch = (none,post)) :
    ∃ child : BitVec 64, post.locals.lookup (ofString "node") = some (.val (.word child)) ∧
      (child = 0 ∨ child ∈ live) ∧ trieWalkLoopRank length post < trieWalkLoopRank length state ∧
      BranchChildrenIn live branches post ∧ TrieNibbleRange post nibs length ∧
      post.memory = state.memory ∧ post.globals = state.globals := by
  have beforeEnd := evaluate_trieWalk_branch_normal_before_end state post index length posLocal nlenLocal bounded run
  obtain ⟨byte,child,read,_,loaded,childLocal⟩ := evaluate_trieWalk_branch_child_address state post node nibs index nodeLocal nibsLocal posLocal run
  have literal : BitVec.ofNat 64 index.toNat = index := by simp
  have slotBound : byte.toNat < 16 := nibbles index.toNat beforeEnd byte (by simpa only [literal] using read)
  have liveChild := children node member byte.toNat slotBound child loaded
  have decrease := evaluate_trieWalk_branch_traversal_rank state post index length node child posLocal nlenLocal nodeLocal childLocal bounded run
  have rankDecrease := trieWalkLoopRank_decreases state post node child length nodeLocal childLocal nodeNonzero decrease
  obtain ⟨_,_,memory,globals,_⟩ := evaluate_trieWalk_branch_normal_position state post index posLocal run
  have metadata := evaluateHOLFiniteState_metadata state trieWalkBranchBranch
  rw [run] at metadata
  dsimp only at metadata
  exact ⟨child,childLocal,liveChild,rankDecrease,children.after_memory memory,
    nibbles.after_frame memory metadata.2.1 metadata.2.2.1,memory,globals⟩

#print axioms evaluate_trieWalk_branch_registry_transition
end InitECandidate.Runtime
