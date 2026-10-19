import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A first component that cannot fall through determines the whole sequence. -/
theorem evaluate_sequence_stopped {F : Type} (state : PanSemStateFiniteExact 64 F)
    (first tail : ProgHOL 64) (stopped : (evaluateHOLFiniteState state first).1 ≠ none) :
    evaluateHOLFiniteState state (.seq first tail) = evaluateHOLFiniteState state first := by
  rw [evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState state first with
  | mk result post =>
    rw [run] at stopped
    cases result with
    | none => exact False.elim (stopped rfl)
    | some result => rfl

#print axioms evaluate_sequence_stopped
end InitECandidate.Runtime
