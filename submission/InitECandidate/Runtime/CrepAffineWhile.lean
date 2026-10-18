import InitECandidate.Runtime.CrepAffineControl
namespace InitECandidate.Runtime
open Flapjack

theorem affine_tick_split (R s m f : Nat) (hm : m ≤ s - 1) (hf : f ≤ m) (pos : 1 ≤ s) :
    R * (s - 1 - m) + R * (m - f) + R = R * (s - f) := by
  have split : s - f = (s - 1 - m) + (m - f) + 1 := by omega
  rw [split, Nat.mul_add, Nat.mul_add, Nat.mul_one]

theorem affine_tick_end (R s m : Nat) (hm : m ≤ s - 1) (pos : 1 ≤ s) :
    R * (s - 1 - m) + R = R * (s - m) := by
  have split : s - m = (s - 1 - m) + 1 := by omega
  rw [split, Nat.mul_add, Nat.mul_one]

/-- Continuation budget only after an actual normal or continue-0 iteration. -/
noncomputable def crepWhileRestBudget {width : Nat} [NeZero width] {F : Type}
    (limit : Nat) (e : CrepExpHOL width) (body : CrepProgHOL width) (s : CrepSemHOLState width F) : Nat :=
  match evalCrepSemHOLProgExact (decClockCrepSemHOL s) body with
  | (none, post) => crepAffine limit (.while e body) post
  | (some (.continue 0), post) => crepAffine limit (.while e body) post
  | _ => 0

/-- Iteration budgets are charged only when the condition holds and a clock is available. -/
noncomputable def crepWhileGuard {width : Nat} [NeZero width] {F : Type}
    (e : CrepExpHOL width) (s : CrepSemHOLState width F) (amount : Nat) : Nat :=
  match evalCrepSemHOLExp s e with
  | some (.word w) => if w ≠ 0 ∧ s.clock ≠ 0 then amount else 0
  | _ => 0

theorem crep_while_affine {width : Nat} [NeZero width] {F : Type}
    (limit : Nat) (e : CrepExpHOL width) (body : CrepProgHOL width)
    (s : CrepSemHOLState width F) (small : sizeOf (CrepProgHOL.while e body) ≤ limit)
    (bounded : CrepCodeSize limit s) (ih : CrepAffineIH limit (.while e body) s) :
    BoundedCrepPropertyAt (.while e body) s (crepAffine limit (.while e body) s) := by
  have childSize : sizeOf body < sizeOf (CrepProgHOL.while e body) := by simp; omega
  have he := crepExprFuel_le_size e
  have sizeSpec : sizeOf (CrepProgHOL.while e body) = 1 + sizeOf e + sizeOf body := by simp
  have child : ∀ w, evalCrepSemHOLExp s e = some (.word w) ∧ w ≠ 0 ∧ s.clock ≠ 0 →
      BoundedCrepPropertyAt body (decClockCrepSemHOL s)
        (crepWhileGuard e s (crepAffine limit body (decClockCrepSemHOL s))) := by
    intro w ⟨found, nonzero, positive⟩
    simp only [crepWhileGuard, found, nonzero, positive, ne_eq, not_false_eq_true, and_self, if_true]
    apply ih body _ (workRank_clock _ _ _ _ _ ?_ (by omega)) (by omega) bounded.decClock
    simp only [decClockCrepSemHOL]
    omega
  have recur : ∀ w r post, evalCrepSemHOLExp s e = some (.word w) ∧ w ≠ 0 ∧ s.clock ≠ 0 ∧
      evalCrepSemHOLProgExact (decClockCrepSemHOL s) body = (r, post) ∧ (r = some (.continue 0) ∨ r = none) →
      BoundedCrepPropertyAt (.while e body) post
        (crepWhileGuard e s (crepWhileRestBudget limit e body s)) := by
    intro w r post ⟨found, nonzero, positive, run, cont⟩
    simp only [crepWhileGuard, found, nonzero, positive, ne_eq, not_false_eq_true, and_self, if_true]
    have clock := evalCrepSemHOLProgExact_clock_le (decClockCrepSemHOL s) body
    rw [run] at clock
    have lower : post.clock < s.clock := by
      change post.clock ≤ s.clock - 1 at clock
      omega
    have postBounded : CrepCodeSize limit post := bounded.decClock.evaluated body |>.of_code_eq (by rw [run])
    unfold crepWhileRestBudget
    rw [run]
    rcases cont with rfl | rfl
    · exact ih _ post (workRank_clock _ _ _ _ _ lower small) small postBounded
    · exact ih _ post (workRank_clock _ _ _ _ _ lower small) small postBounded
  have run : BoundedCrepPropertyAt (.while e body) s
      (crepExprFuel e + crepWhileGuard e s (crepAffine limit body (decClockCrepSemHOL s)) +
        crepWhileGuard e s (crepWhileRestBudget limit e body s) + 2) := by
    intro result post target ctxt live hr hg hs hm hgl hc hl
    apply crep_while_bounded_step e body s _ _ ?_ ?_ ?_ result post target ctxt live ⟨hr,hg,hs,hm,hgl,hc,hl⟩
    · intro w r post h
      exact recur w r post ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, Or.inl h.2.2.2.2⟩
    · intro w r post h
      exact recur w r post ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, Or.inr h.2.2.2.2⟩
    · intro w h
      exact child w h
  apply crep_bounded_mono run
  unfold crepAffine
  rw [evalCrepSemHOLProgExact_while_unstamped, crepExactEvalExp_eq_eval]
  cases found : evalCrepSemHOLExp s e with
  | none => simp only [crepWhileGuard, found]; omega
  | some value =>
    cases value
    case word w =>
      by_cases zero : w = 0#width
      · simp [crepWhileGuard, found, zero]; omega
      · by_cases clockZero : s.clock = 0
        · simp [crepWhileGuard, found, zero, clockZero, CrepSemHOLState.emptyLocals]; omega
        · simp only [crepWhileGuard, found, zero, clockZero, ne_eq, not_false_eq_true, and_self, if_true,
            dif_neg clockZero, if_false]
          rw [fixClockCrepSemHOL_evalCrepSemHOLProgExact]
          cases bodyRun : evalCrepSemHOLProgExact (decClockCrepSemHOL s) body with
          | mk bodyResult middle =>
            have bodyClock : middle.clock ≤ s.clock - 1 := by
              have h := evalCrepSemHOLProgExact_clock_le (decClockCrepSemHOL s) body
              rw [bodyRun] at h; exact h
            have bodyEq : crepAffine limit body (decClockCrepSemHOL s) =
                (5 * limit + 5) * (s.clock - 1 - middle.clock) + 2 * sizeOf body := by
              unfold crepAffine; rw [bodyRun]; rfl
            have zero' : ¬ w = 0 := zero
            have positive : 1 ≤ s.clock := by omega
            have limitBody : sizeOf body ≤ limit := by omega
            have decClock' : (decClockCrepSemHOL s).clock = s.clock - 1 := rfl
            unfold crepWhileRestBudget
            rw [bodyRun]
            simp only [zero', decClock', not_false_eq_true, and_true, if_true, dite_false]
            have ending := affine_tick_end (5 * limit + 5) s.clock middle.clock bodyClock positive
            cases bodyResult with
            | none =>
              simp only
              unfold crepAffine
              have finalClock := evalCrepSemHOLProgExact_clock_le middle (.while e body)
              have ticking := affine_tick_split (5 * limit + 5) s.clock middle.clock _ bodyClock finalClock positive
              omega
            | some r =>
              cases r
              case «continue» n =>
                cases n with
                | zero =>
                  simp only
                  unfold crepAffine
                  have finalClock := evalCrepSemHOLProgExact_clock_le middle (.while e body)
                  have ticking := affine_tick_split (5 * limit + 5) s.clock middle.clock _ bodyClock finalClock positive
                  omega
                | succ n => simp only; omega
              case «break» n =>
                cases n with
                | zero => simp only; omega
                | succ n => simp only; omega
              all_goals simp only; omega
    all_goals simp only [crepWhileGuard, found]; omega

#print axioms crep_while_affine
end InitECandidate.Runtime
