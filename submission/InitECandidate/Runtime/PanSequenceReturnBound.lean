import InitECandidate.Runtime.FrameHalt
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Appending return-zero consumes no additional source clock, and guarantees
a terminal result even when the preceding statement completed normally. -/
theorem evaluate_sequence_return_zero {F : Type} (state : PanSemStateFiniteExact 64 F) (program : ProgHOL 64) :
    (evaluateHOLFiniteState state (.seq program (.return (.const 0)))).2.clock =
      (evaluateHOLFiniteState state program).2.clock ∧
    (evaluateHOLFiniteState state (.seq program (.return (.const 0)))).1 ≠ none := by
  rw [evaluateHOLFiniteState_seq]
  dsimp only
  rw [fixClockHOLFinite_evaluateState]
  cases run : evaluateHOLFiniteState state program with
  | mk result post =>
    cases result with
    | none => simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,emptyLocalsHOLFinite]
    | some result => simp

#print axioms evaluate_sequence_return_zero
end InitECandidate.Runtime
