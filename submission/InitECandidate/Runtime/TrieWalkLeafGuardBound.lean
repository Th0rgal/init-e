import InitECandidate.Runtime.TrieWalkComparisonArguments
import InitECandidate.Runtime.PanSeqStraightBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def trieWalkLeafAfterLength : ProgHOL 64 :=
  match trieWalkLeafBranch with | .dec _ _ _ body => body | _ => .skip

def trieWalkLeafLengthCondition : ExpHOL 64 :=
  .cmp .equal (.var .local (ofString "rl")) (.op .sub [.var .local (ofString "nlen"),.var .local (ofString "pos")])

theorem source_trieWalk_leaf_after_length : trieWalkLeafAfterLength =
    .seq (.ite trieWalkLeafLengthCondition trieWalkLeafComparison .skip) trieWalkEmptyReturn := by
  simp only [trieWalkLeafAfterLength,trieWalkLeafBranch,trieWalkLeafComparison,trieWalkStep,trieWalkLoop,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original leaf guard, comparison and final return cost at most257
source ticks. Only a matching remaining length reaches memeq. -/
theorem evaluate_trieWalk_leaf_after_length_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (node nibs pos size nlen : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word pos)))
    (lengthLocal : state.locals.lookup (ofString "rl") = some (.val (.word size)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word nlen)))
    (code : state.code = originalRuntimeCode) (position : pos.toNat ≤ nlen.toNat)
    (keySize : nlen.toNat ≤ 64) (ticks : 257 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state trieWalkLeafAfterLength;
    state.clock ≤ evaluated.2.clock + 257 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have first : let evaluated := evaluateHOLFiniteState state (.ite trieWalkLeafLengthCondition trieWalkLeafComparison .skip);
      state.clock ≤ evaluated.2.clock + 257 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
    by_cases matchesLength : size = nlen - pos
    · have condition : @evalHOLExact 64 F _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address)) trieWalkLeafLengthCondition =
          some (.val (.word (1 : BitVec 64))) := by
        simp [trieWalkLeafLengthCondition,evalHOLExact,evalListHOLExact,nlenLocal,posLocal,lengthLocal,
          wordOpHOL,wordOp,valueIsWord,valueWord,Compiler.Encoders.Asm.wordCmpHOL,matchesLength]
      have subtract : (nlen - pos).toNat = nlen.toNat - pos.toNat := BitVec.toNat_sub_of_le (BitVec.le_def.mpr position)
      have small : size.toNat ≤ 64 := by rw [matchesLength,subtract]; omega
      have bound := evaluate_trieWalk_comparison_from_locals state (ofString "eq") (ofString "rl")
        trieWalkLeafContinuation trieWalk_leaf_continuation_straightLine node nibs pos size
        nodeLocal nibsLocal posLocal lengthLocal code small ticks
      rw [evaluateHOLFiniteState_ite,condition]
      simp only [show ¬(1 : BitVec 64) = 0 by decide,if_false]
      rw [source_trieWalk_leaf_comparison]
      exact bound
    · have condition : @evalHOLExact 64 F _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address)) trieWalkLeafLengthCondition =
          some (.val (.word (0 : BitVec 64))) := by
        simp [trieWalkLeafLengthCondition,evalHOLExact,evalListHOLExact,nlenLocal,posLocal,lengthLocal,
          wordOpHOL,wordOp,valueIsWord,valueWord,Compiler.Encoders.Asm.wordCmpHOL,matchesLength]
      rw [evaluateHOLFiniteState_ite,condition]
      simp only [if_true,evaluateHOLFiniteState_skip]
      exact ⟨by omega,by omega,by simp⟩
  rw [source_trieWalk_leaf_after_length]
  exact evaluate_sequence_straight_bounded state _ _ 257 first rfl

#print axioms source_trieWalk_leaf_after_length
#print axioms evaluate_trieWalk_leaf_after_length_bounded
end InitECandidate.Runtime
