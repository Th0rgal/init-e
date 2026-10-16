import InitECandidate.Runtime.CrepCeilingControl
namespace InitECandidate.Runtime
open Flapjack

theorem crep_call_ceiling {width : Nat} [NeZero width] {F : Type}
    (limit : Nat) (ret : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (name : Flapjack.Basis.Pure.MlString.MlString) (es : List (CrepExpHOL width))
    (s : CrepSemHOLState width F) (small : sizeOf (CrepProgHOL.call ret name es) ≤ limit)
    (bounded : CrepCodeSize limit s) (ih : CrepCeilingIH limit (.call ret name es) s) :
    BoundedCrepPropertyAt (.call ret name es) s
      (workCeiling limit s.clock (sizeOf (CrepProgHOL.call ret name es))) := by
  have expression : crepExpsFuel es ≤ 8 ^ workRank limit s.clock (sizeOf (CrepProgHOL.call ret name es)) := by
    have he := crepExpsFuel_le_size es
    have hp := crep_rank_pow (workRank limit s.clock (sizeOf (CrepProgHOL.call ret name es)))
    simp only [workRank, CrepProgHOL.call.sizeOf_spec] at hp ⊢
    omega
  have lower (positive : s.clock ≠ 0) : (decClockCrepSemHOL s).clock < s.clock := by
    simp only [decClockCrepSemHOL]
    omega
  have run : BoundedCrepPropertyAt (.call ret name es) s
      (crepExpsFuel es + 8 ^ workRank limit s.clock (sizeOf (CrepProgHOL.call ret name es)) +
        8 ^ workRank limit s.clock (sizeOf (CrepProgHOL.call ret name es)) + 3) := by
    intro result post target ctxt live hr hg hs hm hgl hc hl
    apply crep_call_bounded_step ret name es s _ _ ?_ ?_ result post target ctxt live ⟨hr,hg,hs,hm,hgl,hc,hl⟩
    · intro args prog locals st eid rts handler h
      have positive := h.2.2.2.1
      have called := h.2.2.2.2.1
      have installed := h.2.2.2.2.2
      have clock := evalCrepSemHOLProgExact_clock_le {decClockCrepSemHOL s with locals := locals} prog
      rw [called] at clock
      have less : st.clock < s.clock := Nat.lt_of_le_of_lt clock (lower positive)
      have handlerSize : sizeOf handler < sizeOf (CrepProgHOL.call ret name es) := by
        rw [installed]
        simp
        omega
      apply ih handler {st with locals := s.locals} (workRank_clock _ _ _ _ _ less (by omega)) (by omega)
      have stateBounded := bounded.decClock.setLocals locals
      have postBounded := stateBounded.evaluated prog
      have stBounded : CrepCodeSize limit st := postBounded.of_code_eq (by rw [called])
      exact stBounded.setLocals _
    · intro args prog locals h
      have bodySize := bounded.lookup name args prog locals h.2.1
      exact ih prog _ (workRank_clock _ _ _ _ _ (lower h.2.2.2) bodySize) bodySize
        (bounded.decClock.setLocals locals)
  apply crep_bounded_mono run
  exact crep_ceiling_sum _ _ _ _ expression (Nat.le_refl _) (Nat.le_refl _)

#print axioms crep_call_ceiling
end InitECandidate.Runtime
