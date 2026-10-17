import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A while loop cannot return a value if no execution of its body can return
one, including continue, failed guards, fuel exhaustion and exceptional exits. -/
theorem evaluate_while_no_return {F : Type} (condition : ExpHOL 64) (body : ProgHOL 64)
    (bodyNoReturn : ∀ state : PanSemStateFiniteExact 64 F, ∀ value : ValueHOL 64,
      (evaluateHOLFiniteState state body).1 ≠ some (.returned value))
    (state : PanSemStateFiniteExact 64 F) (value : ValueHOL 64) :
    (evaluateHOLFiniteState state (.while condition body)).1 ≠ some (.returned value) := by
  classical
  have visit : ∀ n : Nat, ∀ current : PanSemStateFiniteExact 64 F, current.clock = n →
      (evaluateHOLFiniteState current (.while condition body)).1 ≠ some (.returned value) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro current distance
      rw [evaluateHOLFiniteState_while_total]
      split
      · rename_i word guard
        by_cases enabled : word ≠ 0
        · rw [if_pos enabled]
          by_cases zero : current.clock = 0
          · simp [zero]
          · rw [if_neg zero]
            cases run : evaluateHOLFiniteState (decClockHOLFinite current) body with
            | mk result next =>
              have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite current) body
              rw [run] at remaining
              have fixed : fixClockHOLFinite (decClockHOLFinite current) (result,next) = (result,next) := by
                simp [fixClockHOLFinite,Nat.not_lt.mpr remaining]
              simp only [run,fixed]
              have smaller : next.clock < n := by
                change next.clock ≤ current.clock - 1 at remaining
                omega
              have safe := bodyNoReturn (decClockHOLFinite current) value
              rw [run] at safe
              cases result with
              | none => exact ih next.clock smaller next rfl
              | some result =>
                cases result with
                | «continue» => exact ih next.clock smaller next rfl
                | «break» => simp
                | returned returnedValue => exact safe
                | error => simp
                | timeOut => simp
                | exception exception exceptionValue => simp
                | finalFfi ffi => simp
        · have zero : word = 0#64 := by
            apply Classical.byContradiction
            intro notZero
            exact enabled notZero
          simp [zero]
      · simp
  exact visit state.clock state rfl

#print axioms evaluate_while_no_return
end InitECandidate.Runtime
