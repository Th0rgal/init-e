import InitECandidate.Runtime.NormalWhileLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Normal completion transports a body invariant through the actual loop,
using source-clock descent and excluding direct break/continue exits. -/
theorem evaluate_normal_while_invariant_by_control {F : Type} (condition : ExpHOL 64) (body : ProgHOL 64)
    (invariant : PanSemStateFiniteExact 64 F → Prop)
    (enter : ∀ state, invariant state → invariant (decClockHOLFinite state))
    (step : ∀ state post, invariant state → evaluateHOLFiniteState state body = (none,post) → invariant post)
    (control : ∀ current : PanSemStateFiniteExact 64 F,
      (evaluateHOLFiniteState current body).1 ≠ some .break ∧
      (evaluateHOLFiniteState current body).1 ≠ some .continue)
    (state post : PanSemStateFiniteExact 64 F) (valid : invariant state)
    (run : evaluateHOLFiniteState state (.while condition body) = (none,post)) : invariant post := by
  rw [evaluateHOLFiniteState_while_total] at run
  split at run
  · split at run
    · split at run
      · cases run
      · rename_i nonzero
        dsimp only at run
        rw [fixClockHOLFinite_evaluateState] at run
        have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
        have noControl := control (decClockHOLFinite state)
        cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
        | mk result middle =>
          rw [bodyRun] at run remaining noControl
          dsimp only at run remaining noControl
          have smaller : middle.clock < state.clock := by
            change middle.clock ≤ state.clock - 1 at remaining
            omega
          cases result with
          | none =>
            exact evaluate_normal_while_invariant_by_control condition body invariant enter step control middle post
              (step _ _ (enter state valid) bodyRun) run
          | some result => cases result <;> simp_all
    · have equal := (Prod.mk.inj run).2
      rw [← equal]
      exact valid
  · cases run
termination_by state.clock

#print axioms evaluate_normal_while_invariant_by_control
end InitECandidate.Runtime
