import InitECandidate.Runtime.SourceClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A source store either completes or reports an error. Its expression and
memory checks consume no clock and never modify local bindings. -/
theorem evaluate_store_control_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination value : ExpHOL 64) :
    ((evaluateHOLFiniteState state (.store destination value)).1 = none ∨
      (evaluateHOLFiniteState state (.store destination value)).1 = some .error) ∧
    (evaluateHOLFiniteState state (.store destination value)).2.locals = state.locals ∧
    (evaluateHOLFiniteState state (.store destination value)).2.clock = state.clock := by
  rw [evaluateHOLFiniteState_store]
  split
  · split
    · split <;> simp
    · simp
  · simp

#print axioms evaluate_store_control_frame
end InitECandidate.Runtime
