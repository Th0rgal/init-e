import InitECandidate.Runtime.TrieWalkExtensionBranchProgress
import InitECandidate.Runtime.TrieWalkTraversalRank
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Combined-rank decrease for the complete original extension branch.
The child-order premise is tied to the actual loaded zero-length word. Its
establishment from trie construction is deliberately a separate obligation. -/
theorem evaluate_trieWalk_extension_branch_rank {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (node child nibs index length : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (childLocal : post.locals.lookup (ofString "node") = some (.val (.word child)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (bounded : index.toNat ≤ length.toNat)
    (emptyChildOrder : state.memory (node + BitVec.ofNat 64 40) = .word 0 → child.toNat < node.toNat)
    (run : evaluateHOLFiniteState state trieWalkExtensionBranch = (none,post)) :
    trieWalkTraversalRank length post < trieWalkTraversalRank length state := by
  obtain ⟨size,_,loaded,advanced,_,within,_,_,_⟩ := evaluate_trieWalk_extension_branch_progress
    state post node nibs index length nodeLocal nibsLocal posLocal nlenLocal code bounded run
  have nextNat : (index + size).toNat = index.toNat + size.toNat := by
    rw [BitVec.toNat_add_of_lt (by have limit := length.isLt; change index.toNat + size.toNat < 2 ^ 64; omega)]
  simp only [trieWalkTraversalRank,posLocal,nodeLocal,advanced,childLocal]
  rw [nextNat]
  have childLimit := child.isLt
  have nodeLimit := node.isLt
  by_cases zero : size = 0
  · have smaller := emptyChildOrder (by simpa [zero] using loaded)
    simp only [zero]
    omega
  · have positive : 0 < size.toNat := by
      by_contra bad
      apply zero
      apply BitVec.eq_of_toNat_eq
      change size.toNat = 0
      omega
    omega

#print axioms evaluate_trieWalk_extension_branch_rank
end InitECandidate.Runtime
