import InitECandidate.Runtime.TrieWalkExtensionProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Remaining nibbles dominate the entire64-bit node-address range. The
address component makes room for zero-length extensions in an acyclic trie. -/
def trieWalkTraversalRank {F : Type} (length : BitVec 64) (state : PanSemStateFiniteExact 64 F) : Nat :=
  match state.locals.lookup (ofString "pos"),state.locals.lookup (ofString "node") with
  | some (.val (.word index)),some (.val (.word node)) => (length.toNat - index.toNat) * 2^64 + node.toNat
  | _,_ => 0

/-- Trie-sized keys give a finite numerical ceiling for this combined rank. -/
theorem trieWalkTraversalRank_lt {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index node length : BitVec 64)
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (keySize : length.toNat ≤ 64) :
    trieWalkTraversalRank length state < 65 * 2^64 := by
  simp only [trieWalkTraversalRank,posLocal,nodeLocal]
  have limit := node.isLt
  omega

/-- Extension progress for the combined rank. The explicit child-order premise
is needed only for zero-length segments; proving it from trie construction is
a separate obligation, not an implicit positive-length assumption. -/
theorem evaluate_trieWalk_extension_traversal_rank {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (index size length node child : BitVec 64)
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "sl") = some (.val (.word size)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word length)))
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (childLocal : post.locals.lookup (ofString "node") = some (.val (.word child)))
    (within : index.toNat + size.toNat ≤ length.toNat)
    (emptyChildOrder : size = 0 → child.toNat < node.toNat)
    (run : evaluateHOLFiniteState state trieWalkExtensionContinuation = (none,post)) :
    trieWalkTraversalRank length post < trieWalkTraversalRank length state := by
  obtain ⟨advanced,_,nextNat,_,_,_,_,_,_,_⟩ :=
    evaluate_trieWalk_extension_continuation_progress state post index size length posLocal sizeLocal nlenLocal within run
  simp only [trieWalkTraversalRank,posLocal,nodeLocal,advanced,childLocal]
  rw [nextNat]
  have childLimit := child.isLt
  have nodeLimit := node.isLt
  by_cases zero : size = 0
  · have smaller := emptyChildOrder zero
    simp only [zero]
    omega
  · have positive : 0 < size.toNat := by
      by_contra bad
      apply zero
      apply BitVec.eq_of_toNat_eq
      change size.toNat = 0
      omega
    omega

/-- A successful branch-node child transition decreases the combined rank
regardless of the selected child's address. -/
theorem evaluate_trieWalk_branch_traversal_rank {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (index length node child : BitVec 64)
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word length)))
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (childLocal : post.locals.lookup (ofString "node") = some (.val (.word child)))
    (bounded : index.toNat ≤ length.toNat)
    (run : evaluateHOLFiniteState state trieWalkBranchBranch = (none,post)) :
    trieWalkTraversalRank length post < trieWalkTraversalRank length state := by
  have beforeEnd := evaluate_trieWalk_branch_normal_before_end state post index length posLocal nlenLocal bounded run
  have nextNat : (index + 1).toNat = index.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by have limit := length.isLt; change index.toNat + 1 < 2 ^ 64; omega)]
    rfl
  obtain ⟨advanced,_,_,_,_⟩ := evaluate_trieWalk_branch_normal_position state post index posLocal run
  simp only [trieWalkTraversalRank,posLocal,nodeLocal,advanced,childLocal]
  rw [nextNat]
  have childLimit := child.isLt
  have nodeLimit := node.isLt
  omega

#print axioms evaluate_trieWalk_branch_traversal_rank
#print axioms trieWalkTraversalRank_lt
#print axioms evaluate_trieWalk_extension_traversal_rank
end InitECandidate.Runtime
