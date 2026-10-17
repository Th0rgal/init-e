import InitECandidate.Runtime.TrieWalkComparisonsBound
import InitECandidate.Runtime.MemeqDecCall64ValuesBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A trie comparison's argument load either fails or supplies scalar values.
This classification does not require the load to succeed. -/
theorem eval_trieWalk_comparison_arguments {F : Type} (state : PanSemStateFiniteExact 64 F)
    (length : MlS) (node nibs pos size : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word pos)))
    (lengthLocal : state.locals.lookup length = some (.val (.word size))) :
    evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      (trieWalkComparisonArguments length) = none ∨
    ∃ left : HolWordLab 64, evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      (trieWalkComparisonArguments length) = some [.val left,.val (.word (nibs + pos)),.val (.word size)] := by
  classical
  by_cases accessible : state.memaddrs (node + BitVec.ofNat 64 32)
  · right
    refine ⟨state.memory (node + BitVec.ofNat 64 32),?_⟩
    simp [evalListHOLFinite,trieWalkComparisonArguments,evalListHOLExact,evalHOLExact,nodeLocal,nibsLocal,posLocal,lengthLocal,
      wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,accessible]
  · left
    simp [evalListHOLFinite,trieWalkComparisonArguments,evalListHOLExact,evalHOLExact,nodeLocal,nibsLocal,posLocal,lengthLocal,
      wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,accessible]

/-- The actual argument-loading and comparison declaration costs at most257
ticks from typed trie locals, even with inaccessible memory. -/
theorem evaluate_trieWalk_comparison_from_locals {F : Type} (state : PanSemStateFiniteExact 64 F)
    (resultName length : MlS) (continuation : ProgHOL 64) (supported : straightLine continuation = true)
    (node nibs pos size : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word pos)))
    (lengthLocal : state.locals.lookup length = some (.val (.word size)))
    (code : state.code = originalRuntimeCode) (small : size.toNat ≤ 64) (ticks : 257 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.decCall resultName .one (ofString "memeq") (trieWalkComparisonArguments length) continuation);
    state.clock ≤ evaluated.2.clock + 257 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  rcases eval_trieWalk_comparison_arguments state length node nibs pos size nodeLocal nibsLocal posLocal lengthLocal with missing | ⟨left,args⟩
  · rw [evaluateHOLFiniteState_decCall_args_none state resultName .one (ofString "memeq") _ continuation missing]
    dsimp only
    exact ⟨by omega,by omega,by simp⟩
  · have bound := evaluate_memeq_decCall64_values_straight_bounded state resultName continuation supported _ _ _
      left (.word (nibs + pos)) size code args small (by omega)
    dsimp only [trieWalkComparisonArguments] at bound ⊢
    exact ⟨by omega,bound.2.1,bound.2.2⟩

#print axioms eval_trieWalk_comparison_arguments
#print axioms evaluate_trieWalk_comparison_from_locals
end InitECandidate.Runtime
