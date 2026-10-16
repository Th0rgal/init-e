import InitECandidate.Runtime.TrapPrimitiveClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_sequence_preserves_clock {F : Type}
    (state : PanSemStateFiniteExact 64 F) (first second : ProgHOL 64)
    (firstClock : (evaluateHOLFiniteState state first).2.clock = state.clock)
    (secondClock : ∀ next : PanSemStateFiniteExact 64 F,
      (evaluateHOLFiniteState next second).2.clock = next.clock) :
    (evaluateHOLFiniteState state (.seq first second)).2.clock = state.clock := by
  have fixed : fixClockHOLFinite state (evaluateHOLFiniteState state first) = evaluateHOLFiniteState state first := by
    simp [fixClockHOLFinite,← firstClock]
  rw [evaluateHOLFiniteState_seq]
  dsimp only
  rw [fixed]
  split
  · exact (secondClock _).trans firstClock
  · exact firstClock

/-- The original trap body consumes no source clock, including every early
error/final-FFI outcome. The caller's entry clock is accounted for separately. -/
theorem evaluate_trap_body_clock {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_trap_with)).2.clock = state.clock := by
  rw [source_trap_body]
  unfold trapSourceBody
  apply evaluate_sequence_preserves_clock
  · exact evaluate_shared_store_clock _ _ _ _
  · intro next
    apply evaluate_sequence_preserves_clock
    · exact evaluate_shared_store_clock _ _ _ _
    · intro next
      apply evaluate_sequence_preserves_clock
      · exact evaluate_shared_store_clock _ _ _ _
      · intro next
        apply evaluate_sequence_preserves_clock
        · exact evaluate_external_call_clock _ _ _ _ _ _
        · intro next
          exact evaluate_raise_clock _ _ _

theorem evaluate_sequence_terminal {F : Type}
    (state : PanSemStateFiniteExact 64 F) (first second : ProgHOL 64)
    (terminal : ∀ next : PanSemStateFiniteExact 64 F,
      (evaluateHOLFiniteState next second).1 ≠ none) :
    (evaluateHOLFiniteState state (.seq first second)).1 ≠ none := by
  rw [evaluateHOLFiniteState_seq]
  dsimp only
  split
  · exact terminal _
  · simp_all

theorem evaluate_raise_terminal {F : Type} (state : PanSemStateFiniteExact 64 F)
    (exception : MlS) (value : ExpHOL 64) :
    (evaluateHOLFiniteState state (.raise exception value)).1 ≠ none := by
  rw [evaluateHOLFiniteState_raise]
  split
  · dsimp only
    split <;> simp
  · simp

theorem evaluate_trap_body_terminal {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_trap_with)).1 ≠ none := by
  rw [source_trap_body]
  unfold trapSourceBody
  apply evaluate_sequence_terminal
  intro next
  apply evaluate_sequence_terminal
  intro next
  apply evaluate_sequence_terminal
  intro next
  apply evaluate_sequence_terminal
  intro next
  exact evaluate_raise_terminal _ _ _

#print axioms evaluate_trap_body_terminal
#print axioms evaluate_sequence_preserves_clock
#print axioms evaluate_trap_body_clock
end InitECandidate.Runtime
