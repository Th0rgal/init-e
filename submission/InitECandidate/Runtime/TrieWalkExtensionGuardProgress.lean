import InitECandidate.Runtime.TrieWalkComparisonProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal completion of the actual extension length guard establishes that
its segment fits the remaining key and reaches the original comparison. -/
theorem evaluate_trieWalk_extension_guard_normal {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (index size length : BitVec 64)
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "sl") = some (.val (.word size)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word length)))
    (bounded : index.toNat ≤ length.toNat)
    (run : evaluateHOLFiniteState state trieWalkExtensionAfterLength = (none,post)) :
    index.toNat + size.toNat ≤ length.toNat ∧
    evaluateHOLFiniteState state trieWalkExtensionComparison = (none,post) := by
  by_cases excess : length - index < size
  · have condition : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) trieWalkExtensionLengthCondition =
        some (.val (.word (1 : BitVec 64))) := by
      simp [trieWalkExtensionLengthCondition,evalHOLExact,evalListHOLExact,nlenLocal,posLocal,sizeLocal,
        wordOpHOL,wordOp,valueIsWord,valueWord,Compiler.Encoders.Asm.wordCmpHOL,excess]
    rw [source_trieWalk_extension_after_length,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition] at run
    simp [trieWalkEmptyReturn,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,shapeOfHOLExact] at run
  · have condition : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) trieWalkExtensionLengthCondition =
        some (.val (.word (0 : BitVec 64))) := by
      simp [trieWalkExtensionLengthCondition,evalHOLExact,evalListHOLExact,nlenLocal,posLocal,sizeLocal,
        wordOpHOL,wordOp,valueIsWord,valueWord,Compiler.Encoders.Asm.wordCmpHOL,excess]
    have within : size.toNat ≤ (length - index).toNat := by
      by_contra bad
      exact excess (BitVec.lt_def.mpr (by omega))
    have subtract : (length - index).toNat = length.toNat - index.toNat := BitVec.toNat_sub_of_le (BitVec.le_def.mpr bounded)
    refine ⟨by omega,?_⟩
    rw [source_trieWalk_extension_after_length,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition] at run
    simpa only [if_true,evaluateHOLFiniteState_skip] using run

/-- The exact original guard-plus-comparison suffix preserves its key-position
invariant through memeq and scope restoration. Strict position progress is
proved exactly for positive segment lengths; zero lengths remain explicit. -/
theorem evaluate_trieWalk_extension_guard_progress {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (node nibs index size length : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "sl") = some (.val (.word size)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (bounded : index.toNat ≤ length.toNat)
    (run : evaluateHOLFiniteState state trieWalkExtensionAfterLength = (none,post)) :
    post.locals.lookup (ofString "pos") = some (.val (.word (index + size))) ∧
    post.locals.lookup (ofString "nlen") = some (.val (.word length)) ∧
    (index + size).toNat ≤ length.toNat ∧
    trieWalkPositionRank length post ≤ trieWalkPositionRank length state ∧
    (trieWalkPositionRank length post < trieWalkPositionRank length state ↔ 0 < size.toNat) := by
  obtain ⟨within,comparison⟩ := evaluate_trieWalk_extension_guard_normal state post index size length posLocal sizeLocal nlenLocal bounded run
  obtain ⟨advanced,kept⟩ := evaluate_trieWalk_extension_comparison_position state post node nibs index size length
    nodeLocal nibsLocal posLocal sizeLocal nlenLocal code comparison
  obtain ⟨postBound,rankBound,strict⟩ := evaluate_trieWalk_extension_comparison_position_rank state post node nibs index size length
    nodeLocal nibsLocal posLocal sizeLocal nlenLocal code within comparison
  exact ⟨advanced,kept,postBound,rankBound,strict⟩

#print axioms evaluate_trieWalk_extension_guard_normal
#print axioms evaluate_trieWalk_extension_guard_progress
end InitECandidate.Runtime
