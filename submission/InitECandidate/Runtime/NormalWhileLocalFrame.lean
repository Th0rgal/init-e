import InitECandidate.Runtime.NormalLocalFrame
import InitECandidate.Runtime.NoLoopControl
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A normally completed loop preserves a local when each normal body does,
and its body cannot exit via break or continue. Exceptional returns are excluded
by the actual normal completion premise. -/
theorem evaluate_normal_while_local_frame {F : Type} (key : MlS) (condition : ExpHOL 64) (body : ProgHOL 64)
    (frame : normalLocalFrameSyntax key body = true) (control : noLoopControl body = true)
    (state post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState state (.while condition body) = (none,post)) :
    post.locals.lookup key = state.locals.lookup key := by
  rw [evaluateHOLFiniteState_while_total] at run
  split at run
  · split at run
    · split at run
      · cases run
      · rename_i nonzero
        dsimp only at run
        rw [fixClockHOLFinite_evaluateState] at run
        have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
        have noControl := evaluate_noLoopControl body control (decClockHOLFinite state)
        cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
        | mk result middle =>
          rw [bodyRun] at run remaining noControl
          dsimp only at run remaining noControl
          have smaller : middle.clock < state.clock := by
            change middle.clock ≤ state.clock - 1 at remaining
            omega
          cases result with
          | none =>
            have kept := evaluate_normalLocalFrame key body frame (decClockHOLFinite state) middle bodyRun
            exact (evaluate_normal_while_local_frame key condition body frame control middle post run).trans kept
          | some result =>
            cases result <;> simp_all
    · have equal := (Prod.mk.inj run).2
      rw [← equal]
  · cases run
termination_by state.clock

#print axioms evaluate_normal_while_local_frame
end InitECandidate.Runtime
