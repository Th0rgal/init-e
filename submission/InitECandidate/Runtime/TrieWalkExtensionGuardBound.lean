import InitECandidate.Runtime.TrieWalkComparisonArguments
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def trieWalkExtensionAfterLength : ProgHOL 64 :=
  match trieWalkExtensionBranch with | .dec _ _ _ body => body | _ => .skip

def trieWalkExtensionLengthCondition : ExpHOL 64 :=
  .cmp .lower (.op .sub [.var .local (ofString "nlen"),.var .local (ofString "pos")]) (.var .local (ofString "sl"))

theorem source_trieWalk_extension_after_length : trieWalkExtensionAfterLength =
    .seq (.ite trieWalkExtensionLengthCondition trieWalkEmptyReturn .skip) trieWalkExtensionComparison := by
  simp only [trieWalkExtensionAfterLength,trieWalkExtensionBranch,trieWalkExtensionComparison,trieWalkStep,trieWalkLoop,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Once the extension length is loaded, the actual guard and comparison
suffix cost at most257 ticks. Rejected lengths need no comparison budget;
accepted lengths are bounded by the remaining64-nibble trie key. -/
theorem evaluate_trieWalk_extension_after_length_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (node nibs pos size nlen : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word pos)))
    (lengthLocal : state.locals.lookup (ofString "sl") = some (.val (.word size)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word nlen)))
    (code : state.code = originalRuntimeCode) (position : pos.toNat ≤ nlen.toNat)
    (keySize : nlen.toNat ≤ 64) (ticks : 257 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state trieWalkExtensionAfterLength;
    state.clock ≤ evaluated.2.clock + 257 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  by_cases excess : nlen - pos < size
  · have condition : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) trieWalkExtensionLengthCondition =
        some (.val (.word (1 : BitVec 64))) := by
      simp [trieWalkExtensionLengthCondition,evalHOLExact,evalListHOLExact,nlenLocal,posLocal,lengthLocal,
        wordOpHOL,wordOp,valueIsWord,valueWord,Compiler.Encoders.Asm.wordCmpHOL,excess]
    rw [source_trieWalk_extension_after_length,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition]
    simp [trieWalkEmptyReturn,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,shapeOfHOLExact,emptyLocalsHOLFinite]
  · have condition : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) trieWalkExtensionLengthCondition =
        some (.val (.word (0 : BitVec 64))) := by
      simp [trieWalkExtensionLengthCondition,evalHOLExact,evalListHOLExact,nlenLocal,posLocal,lengthLocal,
        wordOpHOL,wordOp,valueIsWord,valueWord,Compiler.Encoders.Asm.wordCmpHOL,excess]
    have within : size.toNat ≤ (nlen - pos).toNat := by
      by_contra bad
      exact excess (BitVec.lt_def.mpr (by omega))
    have subtract : (nlen - pos).toNat = nlen.toNat - pos.toNat := BitVec.toNat_sub_of_le (BitVec.le_def.mpr position)
    have bound := evaluate_trieWalk_comparison_from_locals state (ofString "eq2") (ofString "sl")
      trieWalkExtensionContinuation trieWalk_extension_continuation_straightLine node nibs pos size
      nodeLocal nibsLocal posLocal lengthLocal code (by omega) ticks
    rw [source_trieWalk_extension_after_length,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition]
    simp only [ite_true,evaluateHOLFiniteState_skip]
    rw [source_trieWalk_extension_comparison]
    exact bound

#print axioms source_trieWalk_extension_after_length
#print axioms evaluate_trieWalk_extension_after_length_bounded
end InitECandidate.Runtime
