import InitECandidate.Runtime.SourceClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- All-outcome constant source cost: every run of `program`, whether it returns, errors, raises or
times out, leaves at most `C` ticks spent. Timeouts happen only at clock `0` and keep the clock, so no
budget premise is needed for the inequality itself. -/
def CostBounded {σ : Type} (program : ProgHOL 64) (C : Nat) : Prop :=
  ∀ state : PanSemStateFiniteExact 64 σ,
    state.clock ≤ (evaluateHOLFiniteState state program).2.clock + C

theorem costBounded_zero_of_clockPreserving {σ : Type} (program : ProgHOL 64)
    (h : ClockPreserving (σ := σ) program) : CostBounded (σ := σ) program 0 := by
  intro state
  rw [h state]
  omega

theorem costBounded_mono {σ : Type} (program : ProgHOL 64) {C C' : Nat} (le : C ≤ C')
    (h : CostBounded (σ := σ) program C) : CostBounded (σ := σ) program C' := by
  intro state
  have := h state
  omega

/-- The deprecation wrapper: a straight-line piece costs nothing. -/
theorem costBounded_straightLine {σ : Type} (program : ProgHOL 64)
    (supported : straightLine program = true) : CostBounded (σ := σ) program 0 :=
  costBounded_zero_of_clockPreserving program (clockPreserving_of_straightLine program supported)

/-- Sequential composition adds the two constant costs. -/
theorem costBounded_seq {σ : Type} (first second : ProgHOL 64) {C1 C2 : Nat}
    (one : CostBounded (σ := σ) first C1) (two : CostBounded (σ := σ) second C2) :
    CostBounded (σ := σ) (.seq first second) (C1 + C2) := by
  intro state
  rw [evaluateHOLFiniteState_seq]
  dsimp only
  have fixed : fixClockHOLFinite state (evaluateHOLFiniteState state first) =
      evaluateHOLFiniteState state first := fixClockHOLFinite_evaluateState state first
  rw [fixed]
  have hfirst : state.clock ≤ (evaluateHOLFiniteState state first).2.clock + C1 := one state
  split
  · have hsecond : (evaluateHOLFiniteState state first).2.clock ≤
        (evaluateHOLFiniteState (evaluateHOLFiniteState state first).2 second).2.clock + C2 :=
      two (evaluateHOLFiniteState state first).2
    omega
  · omega

/-- A conditional costs the worse of its two arms. -/
theorem costBounded_ite {σ : Type} (condition : ExpHOL 64) (yes no : ProgHOL 64) {C1 C2 : Nat}
    (hy : CostBounded (σ := σ) yes C1) (hn : CostBounded (σ := σ) no C2) :
    CostBounded (σ := σ) (.ite condition yes no) (max C1 C2) := by
  intro state
  rw [evaluateHOLFiniteState_ite]
  repeat' split
  all_goals first
    | exact Nat.le_add_right _ _
    | (have := hn state; omega)
    | (have := hy state; omega)

#print axioms costBounded_ite
#print axioms costBounded_seq
end InitECandidate.Runtime
