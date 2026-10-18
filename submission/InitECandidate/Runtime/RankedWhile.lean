import InitECandidate.Runtime.CountedLoop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The outcome contract of a ranked while loop, as a predicate on its result pair. -/
def RankedOutcome {F : Type} (state : PanSemStateFiniteExact 64 F) (condition : ExpHOL 64) (budget : Nat)
    (Rank : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat → Prop) (Broke : Prop)
    (r : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F) : Prop :=
  state.clock ≤ r.2.clock + budget ∧ r.2.clock ≤ state.clock ∧ r.1 ≠ some .timeOut ∧
    (r.1 = none → ∃ m, Rank r.2 m ∧ r.2.code = state.code ∧
      (evalHOLFinite r.2 (h := fun a => Classical.propDecidable (r.2.memaddrs a)) condition = some (.val (.word 0)) ∨ Broke))

/-- A while loop whose iterations strictly decrease a natural rank runs within
rank * (cost + 1) ticks in every outcome; a normal exit keeps the rank
invariant and either sees a zero condition or comes from a body `break`
(which must establish `Broke`).  At rank 0 the condition must not evaluate to a nonzero word; from
rank n + 1 with a nonzero condition, the body (run after the loop's tick) is
bounded by `cost` in every outcome, and every normal or `continue` outcome
lands at rank at most n. -/
theorem rankedWhile_run (condition : ExpHOL 64) (body : ProgHOL 64) (cost : Nat)
    (Rank : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat → Prop) (Broke : Prop)
    (exit : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), Rank s 0 → ∀ w : BitVec 64,
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) condition = some (.val (.word w)) → w = 0)
    (step : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (n : Nat) (w : BitVec 64), s.code = originalRuntimeCode →
      Rank s (n + 1) →
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) condition = some (.val (.word w)) →
      w ≠ 0 → cost + 1 ≤ s.clock →
      s.clock - 1 ≤ (evaluateHOLFiniteState (decClockHOLFinite s) body).2.clock + cost ∧
        (evaluateHOLFiniteState (decClockHOLFinite s) body).2.clock ≤ s.clock - 1 ∧
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 ≠ some .timeOut ∧
        ((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
            (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue →
          ∃ m, m ≤ n ∧ Rank (evaluateHOLFiniteState (decClockHOLFinite s) body).2 m ∧
            (evaluateHOLFiniteState (decClockHOLFinite s) body).2.code = s.code) ∧
        ((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .break → Broke ∧
          ∃ m, Rank (evaluateHOLFiniteState (decClockHOLFinite s) body).2 m ∧
            (evaluateHOLFiniteState (decClockHOLFinite s) body).2.code = s.code)) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      Rank state n → n * (cost + 1) ≤ state.clock →
      RankedOutcome state condition (n * (cost + 1)) Rank Broke (evaluateHOLFiniteState state (.while condition body)) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F state code ranked budget
    rw [evaluateHOLFiniteState_while_total]
    split
    · rename_i w hw
      by_cases zero : w = 0
      · subst zero
        simp only [ne_eq,not_true_eq_false,if_false]
        exact ⟨Nat.le_add_right _ _,le_refl _,by simp,fun _ => ⟨n,ranked,rfl,Or.inl hw⟩⟩
      · rw [if_pos zero]
        cases n with
        | zero => exact absurd (exit state ranked w hw) zero
        | succ k =>
          have oneIteration : cost + 1 ≤ (k + 1) * (cost + 1) := Nat.le_mul_of_pos_left _ (by omega)
          have clock : state.clock ≠ 0 := by omega
          rw [if_neg clock]
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have stepRun := step state k w code ranked hw zero (by omega)
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at stepRun
            dsimp only at stepRun
            obtain ⟨spent,kept,safe,advance,broken⟩ := stepRun
            have again : ∀ m, m ≤ k → Rank middle m → middle.code = state.code →
                RankedOutcome state condition ((k + 1) * (cost + 1)) Rank Broke
                  (evaluateHOLFiniteState middle (.while condition body)) := by
              intro m small rankedNext nextCode
              have mono : m * (cost + 1) ≤ k * (cost + 1) := Nat.mul_le_mul_right _ small
              have expand : (k + 1) * (cost + 1) = k * (cost + 1) + (cost + 1) := Nat.succ_mul _ _
              obtain ⟨t1,t2,t3,t4⟩ := ih m (by omega) middle (nextCode.trans code) rankedNext (by omega)
              refine ⟨by omega,by omega,t3,fun normal => ?_⟩
              obtain ⟨m',r',c',e'⟩ := t4 normal
              exact ⟨m',r',c'.trans nextCode,e'⟩
            cases result with
            | none =>
              obtain ⟨m,small,rankedNext,nextCode⟩ := advance (Or.inl rfl)
              exact again m small rankedNext nextCode
            | some r =>
              cases r with
              | «continue» =>
                obtain ⟨m,small,rankedNext,nextCode⟩ := advance (Or.inr rfl)
                exact again m small rankedNext nextCode
              | «break» =>
                obtain ⟨flag,m,rankedNext,nextCode⟩ := broken rfl
                exact ⟨by simp; omega,by simp; omega,by simp,fun _ => ⟨m,rankedNext,nextCode,Or.inr flag⟩⟩
              | timeOut => exact absurd rfl safe
              | _ => exact ⟨by simp; omega,by simp; omega,by simp,by simp⟩
    · exact ⟨Nat.le_add_right _ _,le_refl _,by simp,by simp⟩

#print axioms rankedWhile_run
end InitECandidate.Runtime
