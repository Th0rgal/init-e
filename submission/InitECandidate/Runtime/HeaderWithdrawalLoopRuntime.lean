import InitECandidate.Runtime.CountedLoop
import InitECandidate.Runtime.HeaderWithdrawalLoopFrame
import InitECandidate.Runtime.EncodeWithdrawalCallBound
import InitECandidate.Runtime.SourceCostAdapter
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- A straight-line program costs no tick from any state, with no code premise. -/
theorem runBounded_zero_of_extStraightLine {F : Type} (state : PanSemStateFiniteExact 64 F)
    (program : ProgHOL 64) (supported : extStraightLine program = true) : RunBounded state program 0 := by
  have clock := clockPreserving_of_extStraightLine (F := F) program supported state
  refine ⟨by rw [clock]; omega, by rw [clock], ?_⟩
  exact evaluate_extStraightLine_no_timeout program supported state

/-- The two stores of one iteration are straight-line: their run costs no tick. -/
theorem wdSliceLoopStores_extStraightLine : extStraightLine wdSliceLoopStores = true := by
  decide_cbv


/-- **Counted loop clock bound with state-dependent per-iteration bounds.** This is the `RunBounded`
analogue of `countedWhile_run`: the per-iteration cost is not required to be a uniform `ProgBounded`,
only a `RunBounded` under a preserved state predicate `P`. -/
theorem countedWhile_runBounded (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower)
    (K step : BitVec 64) (small : K.toNat + step.toNat < 2 ^ 63) (positive : 0 < step.toNat)
    {body : ProgHOL 64} {cost : Nat}
    (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (run : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64), P state →
      state.code = originalRuntimeCode →
      state.locals.lookup counter = some (.val (.word w)) → RunBounded state body cost)
    (keep : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64), P state →
      state.code = originalRuntimeCode →
      state.locals.lookup counter = some (.val (.word w)) →
      (evaluateHOLFiniteState state body).1 = none → P (evaluateHOLFiniteState state body).2)
    (advance : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64), P state →
      state.locals.lookup counter = some (.val (.word w)) →
      (evaluateHOLFiniteState state body).1 = none →
      (evaluateHOLFiniteState state body).2.locals.lookup counter = some (.val (.word (w + step))) ∧
      (evaluateHOLFiniteState state body).2.code = state.code)
    (noContinue : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64), P state →
      (evaluateHOLFiniteState state body).1 ≠ some .continue)
    (decrease : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), P state → P (decClockHOLFinite state)) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), P state →
      state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) → w.toNat ≤ K.toNat + step.toNat →
      K.toNat - w.toNat = n → n * (cost + 1) ≤ state.clock →
      state.clock ≤ (evaluateHOLFiniteState state
        (.while (.cmp op (.var .local counter) (.const K)) body)).2.clock + n * (cost + 1) ∧
        (evaluateHOLFiniteState state
          (.while (.cmp op (.var .local counter) (.const K)) body)).2.clock ≤ state.clock ∧
        (evaluateHOLFiniteState state
          (.while (.cmp op (.var .local counter) (.const K)) body)).1 ≠ some .timeOut := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F state pstate code w atCounter within distance budget
    have condition := eval_counted_condition state counter op hop K w (by omega) (by omega) atCounter
    rw [evaluateHOLFiniteState_while_total, condition]
    by_cases lt : w.toNat < K.toNat
    · rw [if_pos lt]
      simp only [show (1 : BitVec 64) ≠ 0 by decide, if_true, ne_eq, not_false_eq_true]
      have positiveRank : 0 < n := by omega
      have clock : state.clock ≠ 0 := by
        have : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
        omega
      rw [if_neg clock]
      rw [fixClockHOLFinite_evaluateState]
      have pclock : P (decClockHOLFinite state) := decrease state pstate
      have codeClock : (decClockHOLFinite state).code = originalRuntimeCode := by
        simpa [decClockHOLFinite] using code
      have atClock : (decClockHOLFinite state).locals.lookup counter = some (.val (.word w)) := by
        simpa [decClockHOLFinite] using atCounter
      have stepRun := run (decClockHOLFinite state) w pclock codeClock atClock
      unfold RunBounded at stepRun
      have meta' := evaluateHOLFiniteState_metadata (decClockHOLFinite state) body
      cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
      | mk result middle =>
        rw [bodyRun] at stepRun meta'
        obtain ⟨spent, kept, safe⟩ := stepRun
        change state.clock - 1 ≤ middle.clock + cost at spent
        change middle.clock ≤ state.clock - 1 at kept
        have oneIteration : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
        cases result with
        | none =>
          dsimp only
          have adv := advance (decClockHOLFinite state) w pclock atClock (by rw [bodyRun])
          obtain ⟨nextCounter, nextCode⟩ := adv
          have nextCounter' : middle.locals.lookup counter = some (.val (.word (w + step))) := by
            simpa [bodyRun] using nextCounter
          have nextCode' : middle.code = (decClockHOLFinite state).code := by
            simpa [bodyRun] using nextCode
          have keepP : P middle := by
            simpa [bodyRun] using keep (decClockHOLFinite state) w pclock codeClock atClock
              (by rw [bodyRun])
          have natural : (w + step).toNat = w.toNat + step.toNat := BitVec.toNat_add_of_lt (by omega)
          have nextRank : K.toNat - (w + step).toNat < n := by rw [natural]; omega
          have tail := ih (K.toNat - (w + step).toNat) nextRank middle keepP (nextCode'.trans codeClock) (w + step)
            nextCounter' (by rw [natural]; omega) rfl (by
              have : (K.toNat - (w + step).toNat) * (cost + 1) + (cost + 1) ≤ n * (cost + 1) := by
                rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
              omega)
          obtain ⟨t1, t2, t3⟩ := tail
          refine ⟨?_, by omega, t3⟩
          have : (K.toNat - (w + step).toNat) * (cost + 1) + (cost + 1) ≤ n * (cost + 1) := by
            rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
          omega
        | some r =>
          cases r with
          | «continue» =>
            have hc : (evaluateHOLFiniteState (decClockHOLFinite state) body).1 = some .continue := by
              rw [bodyRun]
            exact absurd hc (noContinue (decClockHOLFinite state) w pclock)
          | «break» => exact ⟨by simp; omega, by simp; omega, by simp⟩
          | timeOut => exact absurd rfl safe
          | _ => exact ⟨by simp; omega, by simp; omega, by simp⟩
    · rw [if_neg lt]
      simp

#print axioms countedWhile_runBounded
end InitECandidate.Runtime
