import InitECandidate.Runtime.TrieWalkNullBound
import InitECandidate.Runtime.MemeqDecCall64Bound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def trieWalkLeafBranch : ProgHOL 64 :=
  match trieWalkStep with
  | .dec _ _ _ (.seq _ (.seq (.ite _ yes _) _)) => yes
  | _ => .skip

def trieWalkExtensionBranch : ProgHOL 64 :=
  match trieWalkStep with
  | .dec _ _ _ (.seq _ (.seq _ (.ite _ yes _))) => yes
  | _ => .skip

def trieWalkLeafComparison : ProgHOL 64 :=
  match trieWalkLeafBranch with
  | .dec _ _ _ (.seq (.ite _ yes _) _) => yes
  | _ => .skip

def trieWalkExtensionComparison : ProgHOL 64 :=
  match trieWalkExtensionBranch with
  | .dec _ _ _ (.seq _ call) => call
  | _ => .skip

def trieWalkLeafContinuation : ProgHOL 64 :=
  match trieWalkLeafComparison with | .decCall _ _ _ _ tail => tail | _ => .skip

def trieWalkExtensionContinuation : ProgHOL 64 :=
  match trieWalkExtensionComparison with | .decCall _ _ _ _ tail => tail | _ => .skip

def trieWalkComparisonArguments (length : MlS) : List (ExpHOL 64) :=
  [.load .one (.op .add [.var .local (ofString "node"),.const 32]),
   .op .add [.var .local (ofString "nibs"),.var .local (ofString "pos")],.var .local length]

theorem source_trieWalk_leaf_comparison : trieWalkLeafComparison =
    .decCall (ofString "eq") .one (ofString "memeq") (trieWalkComparisonArguments (ofString "rl")) trieWalkLeafContinuation := by
  simp only [trieWalkLeafComparison,trieWalkLeafBranch,trieWalkLeafContinuation,trieWalkStep,trieWalkLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_trieWalk_extension_comparison : trieWalkExtensionComparison =
    .decCall (ofString "eq2") .one (ofString "memeq") (trieWalkComparisonArguments (ofString "sl")) trieWalkExtensionContinuation := by
  simp only [trieWalkExtensionComparison,trieWalkExtensionBranch,trieWalkExtensionContinuation,trieWalkStep,trieWalkLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem trieWalk_leaf_continuation_straightLine : straightLine trieWalkLeafContinuation = true := by
  simp only [trieWalkLeafContinuation,trieWalkLeafComparison,trieWalkLeafBranch,trieWalkStep,trieWalkLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem trieWalk_extension_continuation_straightLine : straightLine trieWalkExtensionContinuation = true := by
  simp only [trieWalkExtensionContinuation,trieWalkExtensionComparison,trieWalkExtensionBranch,trieWalkStep,trieWalkLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- A leaf's actual comparison and original return continuation together cost
at most257 source ticks for a valid trie path length, including early errors. -/
theorem evaluate_trieWalk_leaf_comparison_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (left right size : BitVec 64) (code : state.code = originalRuntimeCode)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      (trieWalkComparisonArguments (ofString "rl")) = some [.val (.word left),.val (.word right),.val (.word size)])
    (small : size.toNat ≤ 64) (ticks : 257 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state trieWalkLeafComparison;
    state.clock ≤ evaluated.2.clock + 257 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have bound := evaluate_memeq_decCall64_straight_bounded state (ofString "eq") trieWalkLeafContinuation
    trieWalk_leaf_continuation_straightLine _ _ _ left right size code args small (by omega)
  rw [source_trieWalk_leaf_comparison]
  exact ⟨by dsimp only [trieWalkComparisonArguments] at bound ⊢; omega,bound.2.1,bound.2.2⟩

/-- The extension's actual comparison and original position/node updates
have the same257-tick bound, without assuming successful reads. -/
theorem evaluate_trieWalk_extension_comparison_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (left right size : BitVec 64) (code : state.code = originalRuntimeCode)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      (trieWalkComparisonArguments (ofString "sl")) = some [.val (.word left),.val (.word right),.val (.word size)])
    (small : size.toNat ≤ 64) (ticks : 257 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state trieWalkExtensionComparison;
    state.clock ≤ evaluated.2.clock + 257 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have bound := evaluate_memeq_decCall64_straight_bounded state (ofString "eq2") trieWalkExtensionContinuation
    trieWalk_extension_continuation_straightLine _ _ _ left right size code args small (by omega)
  rw [source_trieWalk_extension_comparison]
  exact ⟨by dsimp only [trieWalkComparisonArguments] at bound ⊢; omega,bound.2.1,bound.2.2⟩

#print axioms source_trieWalk_leaf_comparison
#print axioms source_trieWalk_extension_comparison
#print axioms trieWalk_leaf_continuation_straightLine
#print axioms trieWalk_extension_continuation_straightLine
#print axioms evaluate_trieWalk_leaf_comparison_bounded
#print axioms evaluate_trieWalk_extension_comparison_bounded
end InitECandidate.Runtime
