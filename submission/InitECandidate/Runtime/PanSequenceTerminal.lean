import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- An original return never falls through, including failed expression or
return-size checks. -/
theorem evaluate_return_terminal {F : Type} (state : PanSemStateFiniteExact 64 F) (expression : ExpHOL 64) :
    (evaluateHOLFiniteState state (.return expression)).1 ≠ none := by
  rw [evaluateHOLFiniteState_return]
  split
  · simp
  · split <;> simp

/-- A sequence cannot fall through when its tail cannot fall through at any
state, regardless of the first program's outcome or state mutation. -/
theorem evaluate_seq_terminal {F : Type} (state : PanSemStateFiniteExact 64 F) (first tail : ProgHOL 64)
    (terminal : ∀ current : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState current tail).1 ≠ none) :
    (evaluateHOLFiniteState state (.seq first tail)).1 ≠ none := by
  rw [evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState state first with
  | mk result post =>
    cases result with
    | none => exact terminal post
    | some stopped => simp

#print axioms evaluate_return_terminal
#print axioms evaluate_seq_terminal
end InitECandidate.Runtime
