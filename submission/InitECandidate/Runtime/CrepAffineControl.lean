import InitECandidate.Runtime.CrepCeilingCall
namespace InitECandidate.Runtime
open Flapjack

/-- Affine Crep-to-Loop budget at an actual source execution: (5L+5) target
clocks per consumed source clock plus twice the program size. -/
noncomputable def crepAffine {width : Nat} [NeZero width] {F : Type}
    (limit : Nat) (p : CrepProgHOL width) (s : CrepSemHOLState width F) : Nat :=
  (5 * limit + 5) * (s.clock - (evalCrepSemHOLProgExact s p).2.clock) + 2 * sizeOf p

/-- Obligations at strictly smaller clock/syntax ranks. -/
def CrepAffineIH {width : Nat} [NeZero width] {F : Type}
    (limit : Nat) (p : CrepProgHOL width) (s : CrepSemHOLState width F) : Prop :=
  ∀ (child : CrepProgHOL width) (next : CrepSemHOLState width F),
    workRank limit next.clock (sizeOf child) < workRank limit s.clock (sizeOf p) →
    sizeOf child ≤ limit → CrepCodeSize limit next →
    BoundedCrepPropertyAt child next (crepAffine limit child next)

noncomputable def crepDecBudget {width : Nat} [NeZero width] {F : Type}
    (limit name : Nat) (e : CrepExpHOL width) (body : CrepProgHOL width) (s : CrepSemHOLState width F) : Nat :=
  match evalCrepSemHOLExp s e with
  | some value => crepAffine limit body {s with locals := s.locals.updateEq (name,value)}
  | none => 0

noncomputable def crepIfBudget {width : Nat} [NeZero width] {F : Type}
    (limit : Nat) (e : CrepExpHOL width) (yes no : CrepProgHOL width) (s : CrepSemHOLState width F) : Nat :=
  match evalCrepSemHOLExp s e with
  | some (.word w) => crepAffine limit (if w ≠ 0 then yes else no) s
  | _ => 0

theorem crep_leaf_affine {width : Nat} [NeZero width] {F : Type}
    {p : CrepProgHOL width} {s : CrepSemHOLState width F} {cost : Nat}
    (run : BoundedCrepPropertyAt p s cost) (small : cost ≤ sizeOf p) (limit : Nat) :
    BoundedCrepPropertyAt p s (crepAffine limit p s) := by
  apply crep_bounded_mono run
  unfold crepAffine
  omega

theorem crep_seq_affine {width : Nat} [NeZero width] {F : Type}
    (limit : Nat) (a b : CrepProgHOL width) (s : CrepSemHOLState width F)
    (small : sizeOf (CrepProgHOL.seq a b) ≤ limit) (bounded : CrepCodeSize limit s)
    (ih : CrepAffineIH limit (.seq a b) s) :
    BoundedCrepPropertyAt (.seq a b) s (crepAffine limit (.seq a b) s) := by
  have sa : sizeOf a < sizeOf (CrepProgHOL.seq a b) := by simp; omega
  have sb : sizeOf b < sizeOf (CrepProgHOL.seq a b) := by simp; omega
  have total : sizeOf a + sizeOf b ≤ sizeOf (CrepProgHOL.seq a b) := by simp <;> omega
  have first := ih a s (workRank_subprogram _ _ _ _ _ (Nat.le_refl _) sa) (by omega) bounded
  cases ra : evalCrepSemHOLProgExact s a with
  | mk r1 middle =>
    have c1 : middle.clock ≤ s.clock := by
      have h := evalCrepSemHOLProgExact_clock_le s a; rw [ra] at h; exact h
    let secondBudget := match r1 with
      | none => crepAffine limit b middle
      | some _ => 0
    have second : ∀ r post, (r,post) = evalCrepSemHOLProgExact s a → r = none →
        BoundedCrepPropertyAt b post secondBudget := by
      intro r post run isNone
      rw [ra] at run
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
      subst isNone
      exact ih b post (workRank_subprogram _ _ _ _ _ c1 sb) (by omega)
        (bounded.evaluated a |>.of_code_eq (by rw [ra]))
    apply crep_bounded_mono (crep_seq_bounded a b s _ secondBudget second first)
    have firstEq : crepAffine limit a s = (5 * limit + 5) * (s.clock - middle.clock) + 2 * sizeOf a := by
      unfold crepAffine; rw [ra]
    rw [firstEq]
    unfold crepAffine
    rw [evalCrepSemHOLProgExact_seq, fixClockCrepSemHOL_evalCrepSemHOLProgExact, ra]
    cases r1 with
    | none =>
      dsimp only [secondBudget]
      unfold crepAffine
      have c2 := evalCrepSemHOLProgExact_clock_le middle b
      have split : s.clock - (evalCrepSemHOLProgExact middle b).2.clock =
          (s.clock - middle.clock) + (middle.clock - (evalCrepSemHOLProgExact middle b).2.clock) := by omega
      rw [split, Nat.mul_add]
      omega
    | some value =>
      dsimp only [secondBudget]
      omega

theorem crep_dec_affine {width : Nat} [NeZero width] {F : Type}
    (limit name : Nat) (e : CrepExpHOL width) (body : CrepProgHOL width)
    (s : CrepSemHOLState width F) (small : sizeOf (CrepProgHOL.dec name e body) ≤ limit)
    (bounded : CrepCodeSize limit s) (ih : CrepAffineIH limit (.dec name e body) s) :
    BoundedCrepPropertyAt (.dec name e body) s (crepAffine limit (.dec name e body) s) := by
  have childSize : sizeOf body < sizeOf (CrepProgHOL.dec name e body) := by simp; omega
  have expression : crepExprFuel e + sizeOf body ≤ sizeOf (CrepProgHOL.dec name e body) := by
    have he := crepExprFuel_le_size e
    simp only [CrepProgHOL.dec.sizeOf_spec]
    omega
  have child : ∀ value, evalCrepSemHOLExp s e = some value →
      BoundedCrepPropertyAt body {s with locals := s.locals.updateEq (name,value)} (crepDecBudget limit name e body s) := by
    intro value found
    simp only [crepDecBudget, found]
    exact ih body _ (workRank_subprogram _ _ _ _ _ (Nat.le_refl _) childSize)
      (by omega) (bounded.setLocals _)
  apply crep_bounded_mono (crep_dec_bounded name e body s _ child)
  unfold crepAffine
  rw [evalCrepSemHOLProgExact_dec, crepExactEvalExpClassical_eq]
  cases found : evalCrepSemHOLExp s e with
  | none => simp only [crepDecBudget, found]; omega
  | some value =>
    simp only [crepDecBudget, found]
    unfold crepAffine
    have same : (CrepSemHOLState.setVar name value s) = {s with locals := s.locals.updateEq (name,value)} := rfl
    rw [same]
    have lower := evalCrepSemHOLProgExact_clock_le {s with locals := s.locals.updateEq (name,value)} body
    change _ ≤ s.clock at lower
    have hc : ({s with locals := s.locals.updateEq (name, value)} : CrepSemHOLState width F).clock = s.clock := rfl
    simp only [hc]
    omega

theorem crep_if_affine {width : Nat} [NeZero width] {F : Type}
    (limit : Nat) (e : CrepExpHOL width) (yes no : CrepProgHOL width)
    (s : CrepSemHOLState width F) (small : sizeOf (CrepProgHOL.ite e yes no) ≤ limit)
    (bounded : CrepCodeSize limit s) (ih : CrepAffineIH limit (.ite e yes no) s) :
    BoundedCrepPropertyAt (.ite e yes no) s (crepAffine limit (.ite e yes no) s) := by
  have expression : crepExprFuel e + sizeOf yes + sizeOf no + 1 ≤ sizeOf (CrepProgHOL.ite e yes no) := by
    have he := crepExprFuel_le_size e
    simp only [CrepProgHOL.ite.sizeOf_spec]
    omega
  have child : ∀ w, evalCrepSemHOLExp s e = some (.word w) →
      BoundedCrepPropertyAt (if w ≠ 0 then yes else no) s (crepIfBudget limit e yes no s) := by
    intro w found
    simp only [crepIfBudget, found]
    have childSize : sizeOf (if w ≠ 0 then yes else no) < sizeOf (CrepProgHOL.ite e yes no) := by
      split <;> simp <;> omega
    exact ih _ s (workRank_subprogram _ _ _ _ _ (Nat.le_refl _) childSize) (by omega) bounded
  have run : BoundedCrepPropertyAt (.ite e yes no) s (crepExprFuel e + crepIfBudget limit e yes no s + 1) := by
    intro result post target ctxt live hr hg hs hm hgl hc hl
    exact crep_if_bounded_step e yes no s _ child result post target ctxt live ⟨hr,hg,hs,hm,hgl,hc,hl⟩
  apply crep_bounded_mono run
  unfold crepAffine
  rw [evalCrepSemHOLProgExact_ite, crepExactEvalExp_eq_eval]
  cases found : evalCrepSemHOLExp s e with
  | none => simp only [crepIfBudget, found]; omega
  | some value =>
    cases value
    case word w =>
      simp only [crepIfBudget, found]
      by_cases zero : w = 0#width
      · have he := crepExprFuel_le_size e
        simp [zero, crepAffine]; omega
      · have he := crepExprFuel_le_size e
        simp [zero, crepAffine]; omega
    all_goals simp only [crepIfBudget, found]; omega

#print axioms crep_seq_affine
#print axioms crep_dec_affine
#print axioms crep_if_affine
end InitECandidate.Runtime
