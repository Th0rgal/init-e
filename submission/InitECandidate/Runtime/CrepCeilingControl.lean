import InitECandidate.Runtime.CrepCodeSize
import InitECandidate.Runtime.WorkCeiling
namespace InitECandidate.Runtime
open Flapjack

theorem crep_bounded_mono {width : Nat} [NeZero width] {F : Type}
    {p : CrepProgHOL width} {s : CrepSemHOLState width F} {a b : Nat}
    (h : BoundedCrepPropertyAt p s a) (le : a ≤ b) : BoundedCrepPropertyAt p s b := by
  intro result post target ctxt live run good state memory globals code locals
  obtain ⟨extra,small,witness⟩ := h result post target ctxt live run good state memory globals code locals
  exact ⟨extra,Nat.le_trans small le,witness⟩

/-- Uniform induction obligations at smaller source clock/syntax ranks. -/
def CrepCeilingIH {width : Nat} [NeZero width] {F : Type}
    (limit : Nat) (p : CrepProgHOL width) (s : CrepSemHOLState width F) : Prop :=
  ∀ (child : CrepProgHOL width) (next : CrepSemHOLState width F), workRank limit next.clock (sizeOf child) < workRank limit s.clock (sizeOf p) →
    sizeOf child ≤ limit → CrepCodeSize limit next →
    BoundedCrepPropertyAt child next (8 ^ workRank limit s.clock (sizeOf p))

theorem crep_rank_pow (n : Nat) : n ≤ 8 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have positive : 0 < 8 ^ n := Nat.pow_pos (by decide)
    rw [Nat.pow_succ]
    omega

theorem crep_ceiling_sum (rank expression first second : Nat)
    (he : expression ≤ 8 ^ rank) (hf : first ≤ 8 ^ rank) (hs : second ≤ 8 ^ rank) :
    expression + first + second + 3 ≤ 8 ^ (rank + 1) := by
  have positive : 0 < 8 ^ rank := Nat.pow_pos (by decide)
  rw [Nat.pow_succ]
  omega

theorem crep_seq_ceiling {width : Nat} [NeZero width] {F : Type}
    (limit : Nat) (a b : CrepProgHOL width) (s : CrepSemHOLState width F)
    (small : sizeOf (CrepProgHOL.seq a b) ≤ limit) (bounded : CrepCodeSize limit s)
    (ih : CrepCeilingIH limit (.seq a b) s) :
    BoundedCrepPropertyAt (.seq a b) s (workCeiling limit s.clock (sizeOf (CrepProgHOL.seq a b))) := by
  have sa : sizeOf a < sizeOf (CrepProgHOL.seq a b) := by simp; omega
  have sb : sizeOf b < sizeOf (CrepProgHOL.seq a b) := by simp; omega
  have first := ih a s (workRank_subprogram _ _ _ _ _ (Nat.le_refl _) sa) (by omega) bounded
  have second : ∀ r post, (r,post) = evalCrepSemHOLProgExact s a → r = none →
      BoundedCrepPropertyAt b post (8 ^ workRank limit s.clock (sizeOf (CrepProgHOL.seq a b))) := by
    intro r post run _
    have clock := evalCrepSemHOLProgExact_clock_le s a
    rw [← run] at clock
    exact ih b post (workRank_subprogram _ _ _ _ _ clock sb) (by omega)
      (bounded.evaluated a |>.of_code_eq (by rw [← run]))
  apply crep_bounded_mono (crep_seq_bounded a b s _ _ second first)
  have bound := workCeiling_two (workRank limit s.clock (sizeOf (CrepProgHOL.seq a b))) _ _
    (Nat.le_refl _) (Nat.le_refl _)
  unfold workCeiling
  omega

theorem crep_dec_ceiling {width : Nat} [NeZero width] {F : Type}
    (limit name : Nat) (e : CrepExpHOL width) (body : CrepProgHOL width)
    (s : CrepSemHOLState width F) (small : sizeOf (CrepProgHOL.dec name e body) ≤ limit)
    (bounded : CrepCodeSize limit s) (ih : CrepCeilingIH limit (.dec name e body) s) :
    BoundedCrepPropertyAt (.dec name e body) s
      (workCeiling limit s.clock (sizeOf (CrepProgHOL.dec name e body))) := by
  have childSize : sizeOf body < sizeOf (CrepProgHOL.dec name e body) := by simp; omega
  have expression : crepExprFuel e ≤ 8 ^ workRank limit s.clock (sizeOf (CrepProgHOL.dec name e body)) := by
    have he := crepExprFuel_le_size e
    have hp := crep_rank_pow (workRank limit s.clock (sizeOf (CrepProgHOL.dec name e body)))
    simp only [workRank, CrepProgHOL.dec.sizeOf_spec] at hp ⊢
    omega
  have child : ∀ value, evalCrepSemHOLExp s e = some value →
      BoundedCrepPropertyAt body {s with locals := s.locals.updateEq (name,value)}
        (8 ^ workRank limit s.clock (sizeOf (CrepProgHOL.dec name e body))) := by
    intro value _
    exact ih body _ (workRank_subprogram _ _ _ _ _ (Nat.le_refl _) childSize)
      (by omega) (bounded.setLocals _)
  apply crep_bounded_mono (crep_dec_bounded name e body s _ child)
  have bound := crep_ceiling_sum (workRank limit s.clock (sizeOf (CrepProgHOL.dec name e body)))
    _ _ 0 expression (Nat.le_refl _) (Nat.zero_le _)
  unfold workCeiling
  omega

theorem crep_if_ceiling {width : Nat} [NeZero width] {F : Type}
    (limit : Nat) (e : CrepExpHOL width) (yes no : CrepProgHOL width)
    (s : CrepSemHOLState width F) (small : sizeOf (CrepProgHOL.ite e yes no) ≤ limit)
    (bounded : CrepCodeSize limit s) (ih : CrepCeilingIH limit (.ite e yes no) s) :
    BoundedCrepPropertyAt (.ite e yes no) s
      (workCeiling limit s.clock (sizeOf (CrepProgHOL.ite e yes no))) := by
  have expression : crepExprFuel e ≤ 8 ^ workRank limit s.clock (sizeOf (CrepProgHOL.ite e yes no)) := by
    have he := crepExprFuel_le_size e
    have hp := crep_rank_pow (workRank limit s.clock (sizeOf (CrepProgHOL.ite e yes no)))
    simp only [workRank, CrepProgHOL.ite.sizeOf_spec] at hp ⊢
    omega
  have child : ∀ w, evalCrepSemHOLExp s e = some (.word w) →
      BoundedCrepPropertyAt (if w ≠ 0 then yes else no) s
        (8 ^ workRank limit s.clock (sizeOf (CrepProgHOL.ite e yes no))) := by
    intro w _
    have childSize : sizeOf (if w ≠ 0 then yes else no) < sizeOf (CrepProgHOL.ite e yes no) := by
      split <;> simp <;> omega
    exact ih _ s (workRank_subprogram _ _ _ _ _ (Nat.le_refl _) childSize) (by omega) bounded
  have run : BoundedCrepPropertyAt (.ite e yes no) s
      (crepExprFuel e + 8 ^ workRank limit s.clock (sizeOf (CrepProgHOL.ite e yes no)) + 1) := by
    intro result post target ctxt live hr hg hs hm hgl hc hl
    exact crep_if_bounded_step e yes no s _ child result post target ctxt live ⟨hr,hg,hs,hm,hgl,hc,hl⟩
  apply crep_bounded_mono run
  have bound := crep_ceiling_sum (workRank limit s.clock (sizeOf (CrepProgHOL.ite e yes no)))
    _ _ 0 expression (Nat.le_refl _) (Nat.zero_le _)
  unfold workCeiling
  omega

theorem crep_while_ceiling {width : Nat} [NeZero width] {F : Type}
    (limit : Nat) (e : CrepExpHOL width) (body : CrepProgHOL width)
    (s : CrepSemHOLState width F) (small : sizeOf (CrepProgHOL.while e body) ≤ limit)
    (bounded : CrepCodeSize limit s) (ih : CrepCeilingIH limit (.while e body) s) :
    BoundedCrepPropertyAt (.while e body) s
      (workCeiling limit s.clock (sizeOf (CrepProgHOL.while e body))) := by
  have childSize : sizeOf body < sizeOf (CrepProgHOL.while e body) := by simp; omega
  have expression : crepExprFuel e ≤ 8 ^ workRank limit s.clock (sizeOf (CrepProgHOL.while e body)) := by
    have he := crepExprFuel_le_size e
    have hp := crep_rank_pow (workRank limit s.clock (sizeOf (CrepProgHOL.while e body)))
    simp only [workRank, CrepProgHOL.while.sizeOf_spec] at hp ⊢
    omega
  have child (positive : s.clock ≠ 0) :
      BoundedCrepPropertyAt body (decClockCrepSemHOL s)
        (8 ^ workRank limit s.clock (sizeOf (CrepProgHOL.while e body))) := by
    apply ih body _ (workRank_clock _ _ _ _ _ ?_ (by omega)) (by omega) bounded.decClock
    simp only [decClockCrepSemHOL]
    omega
  have recur (r post) (run : evalCrepSemHOLProgExact (decClockCrepSemHOL s) body = (r,post))
      (positive : s.clock ≠ 0) :
      BoundedCrepPropertyAt (.while e body) post
        (8 ^ workRank limit s.clock (sizeOf (CrepProgHOL.while e body))) := by
    have clock := evalCrepSemHOLProgExact_clock_le (decClockCrepSemHOL s) body
    rw [run] at clock
    have lower : post.clock < s.clock := by
      change post.clock ≤ s.clock - 1 at clock
      omega
    exact ih _ post (workRank_clock _ _ _ _ _ lower small) small
      (bounded.decClock.evaluated body |>.of_code_eq (by rw [run]))
  have run : BoundedCrepPropertyAt (.while e body) s
      (crepExprFuel e + 8 ^ workRank limit s.clock (sizeOf (CrepProgHOL.while e body)) +
        8 ^ workRank limit s.clock (sizeOf (CrepProgHOL.while e body)) + 2) := by
    intro result post target ctxt live hr hg hs hm hgl hc hl
    apply crep_while_bounded_step e body s _ _ ?_ ?_ ?_ result post target ctxt live ⟨hr,hg,hs,hm,hgl,hc,hl⟩
    · intro w r post h
      exact recur r post h.2.2.2.1 h.2.2.1
    · intro w r post h
      exact recur r post h.2.2.2.1 h.2.2.1
    · intro w h
      exact child h.2.2
  apply crep_bounded_mono run
  have bound := crep_ceiling_sum (workRank limit s.clock (sizeOf (CrepProgHOL.while e body)))
    _ _ _ expression (Nat.le_refl _) (Nat.le_refl _)
  unfold workCeiling
  omega

#print axioms crep_while_ceiling
#print axioms crep_dec_ceiling
#print axioms crep_if_ceiling
#print axioms crep_seq_ceiling
#print axioms crep_ceiling_sum
end InitECandidate.Runtime
