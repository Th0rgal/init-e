import InitECandidate.Runtime.TrieWalkExtensionAdvance
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Exact progress of the original extension continuation once the accepted
segment length fits the remaining key. Zero-length segments retain the rank;
positive segments strictly decrease it, and neither case wraps the counter. -/
theorem evaluate_trieWalk_extension_continuation_progress {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (index size length : BitVec 64)
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "sl") = some (.val (.word size)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word length)))
    (within : index.toNat + size.toNat ≤ length.toNat)
    (run : evaluateHOLFiniteState state trieWalkExtensionContinuation = (none,post)) :
    post.locals.lookup (ofString "pos") = some (.val (.word (index + size))) ∧
    post.locals.lookup (ofString "nlen") = some (.val (.word length)) ∧
    (index + size).toNat = index.toNat + size.toNat ∧
    (index + size).toNat ≤ length.toNat ∧
    trieWalkPositionRank length post ≤ trieWalkPositionRank length state ∧
    (trieWalkPositionRank length post < trieWalkPositionRank length state ↔ 0 < size.toNat) ∧
    (size = 0 → trieWalkPositionRank length post = trieWalkPositionRank length state) ∧
    post.memory = state.memory ∧ post.globals = state.globals ∧ post.clock = state.clock := by
  have nextNat : (index + size).toNat = index.toNat + size.toNat := by
    rw [BitVec.toNat_add_of_lt (by have limit := length.isLt; change index.toNat + size.toNat < 2 ^ 64; omega)]
  obtain ⟨advanced,locals,memory,globals,clock⟩ :=
    evaluate_trieWalk_extension_normal_position state post index size posLocal sizeLocal run
  have oldRank : trieWalkPositionRank length state = length.toNat - index.toNat := by
    simp [trieWalkPositionRank,posLocal]
  have newRank : trieWalkPositionRank length post = length.toNat - (index + size).toNat := by
    simp [trieWalkPositionRank,advanced]
  refine ⟨advanced,(locals (ofString "nlen") (by decide) (by decide)).trans nlenLocal,
    nextNat,by omega,?_,?_,?_,memory,globals,clock⟩
  · rw [oldRank,newRank,nextNat]; omega
  · rw [oldRank,newRank,nextNat]; omega
  · intro zero
    rw [oldRank,newRank,nextNat,zero]
    simp

#print axioms evaluate_trieWalk_extension_continuation_progress
end InitECandidate.Runtime
