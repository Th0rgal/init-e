import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Compose two clock bounds using the actual state reached by the first
program. Code preservation is intrinsic to the source semantics. -/
theorem evaluate_sequence_code_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (first tail : ProgHOL 64) (firstCost tailCost : Nat)
    (firstBound : state.clock ≤ (evaluateHOLFiniteState state first).2.clock + firstCost ∧
      (evaluateHOLFiniteState state first).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state first).1 ≠ some .timeOut)
    (tailBound : ∀ next : PanSemStateFiniteExact 64 F, next.code = state.code → tailCost ≤ next.clock →
      next.clock ≤ (evaluateHOLFiniteState next tail).2.clock + tailCost ∧
        (evaluateHOLFiniteState next tail).2.clock ≤ next.clock ∧
        (evaluateHOLFiniteState next tail).1 ≠ some .timeOut)
    (budget : firstCost + tailCost ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.seq first tail)
    state.clock ≤ evaluated.2.clock + (firstCost + tailCost) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have metadata := evaluateHOLFiniteState_metadata state first
  rw [evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState state first with
  | mk result next =>
    rw [run] at firstBound metadata
    dsimp only at firstBound metadata ⊢
    cases result with
    | some result =>
      dsimp only
      exact ⟨by have consumed := firstBound.1; omega,firstBound.2⟩
    | none =>
      dsimp only
      have tail := tailBound next metadata.1 (by have consumed := firstBound.1; omega)
      exact ⟨by have a := firstBound.1; have b := tail.1; omega,
        Nat.le_trans tail.2.1 firstBound.2.1,tail.2.2⟩

#print axioms evaluate_sequence_code_bounded
end InitECandidate.Runtime
