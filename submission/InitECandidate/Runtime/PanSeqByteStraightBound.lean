import InitECandidate.Runtime.ByteStraightLine
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Appending byte-writing straight-line code adds no source clock cost, including when
the first program or the continuation exits exceptionally. -/
theorem evaluate_sequence_byteStraight_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (first tail : ProgHOL 64) (cost : Nat)
    (bound : state.clock ≤ (evaluateHOLFiniteState state first).2.clock + cost ∧
      (evaluateHOLFiniteState state first).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state first).1 ≠ some .timeOut)
    (supported : byteStraightLine tail = true) :
    let evaluated := evaluateHOLFiniteState state (.seq first tail);
    state.clock ≤ evaluated.2.clock + cost ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  cases run : evaluateHOLFiniteState state first with
  | mk result middle =>
    rw [run] at bound
    dsimp only at bound
    rw [evaluateHOLFiniteState_seq_line780,run]
    cases result with
    | none =>
      have clock := clockPreserving_of_byteStraightLine tail supported middle
      have noTimeout := evaluate_byteStraightLine_no_timeout tail supported middle
      dsimp only
      exact ⟨by omega,by omega,noTimeout⟩
    | some result => exact bound

#print axioms evaluate_sequence_byteStraight_bounded
end InitECandidate.Runtime
