namespace InitECandidate.Runtime

theorem shift_or_bit (r bit : BitVec 64) (hr : r.toNat < 2^63) (hb : bit.toNat < 2) :
    (r <<< (1 : Nat) ||| bit).toNat = 2 * r.toNat + bit.toNat := by
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft]
  rw [Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega)]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 1) (by omega), Nat.shiftLeft_eq]
  omega

theorem lsr_and_one (a : BitVec 64) (j : Nat) : ((a >>> j) &&& 1#64).toNat = (a.toNat / 2 ^ j) % 2 := by
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight]
  simp [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]

theorem or_pow (q : BitVec 64) (j : Nat) (hj : j < 64) (hq : q.toNat % 2^(j+1) = 0) :
    (q ||| ((1#64 : BitVec 64) <<< j)).toNat = q.toNat + 2^j := by
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft]
  have one : (1#64 : BitVec 64).toNat = 1 := rfl
  rw [one, Nat.shiftLeft_eq, Nat.one_mul]
  have pj : 2^j < 2^64 := Nat.pow_lt_pow_right (by decide) hj
  rw [Nat.mod_eq_of_lt pj]
  obtain ⟨k, hk⟩ : ∃ k, q.toNat = 2^(j+1) * k := ⟨q.toNat / 2^(j+1), (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hq)).symm⟩
  rw [hk, ← Nat.two_pow_add_eq_or_of_lt (i := j+1) (Nat.pow_lt_pow_right (by decide) (by omega)) k]

structure UdivInv (a b q r : BitVec 64) (i : Nat) : Prop where
  pos : 0 < b.toNat
  le : i ≤ 64
  hq : q.toNat = (a.toNat / 2^i / b.toNat) * 2^i
  hr : r.toNat = a.toNat / 2^i % b.toNat

def udivR1 (a r : BitVec 64) (j : Nat) : BitVec 64 := r <<< (1 : Nat) ||| ((a >>> j) &&& 1#64)

theorem udivInv_step (a b q r : BitVec 64) (j : Nat) (inv : UdivInv a b q r (j+1)) :
    let r1 := udivR1 a r j
    (¬ r1 < b → UdivInv a b (q ||| ((1#64 : BitVec 64) <<< j)) (r1 - b) j) ∧
    (r1 < b → UdivInv a b q r1 j) := by
  intro r1
  have hj : j < 64 := by have := inv.le; omega
  have ha := a.isLt
  have pos := inv.pos
  -- P and P'
  have pj : 2^(j+1) = 2 * 2^j := by rw [Nat.pow_succ]; omega
  have pjpos : 0 < 2^j := Nat.two_pow_pos j
  have hP : a.toNat / 2^(j+1) = a.toNat / 2^j / 2 := by rw [pj, Nat.mul_comm, Nat.div_div_eq_div_mul]
  have bitEq : ((a >>> j) &&& 1#64).toNat = (a.toNat / 2^j) % 2 := lsr_and_one a j
  have rsmall : r.toNat < 2^63 := by
    have h1 : r.toNat ≤ a.toNat / 2^(j+1) := by rw [inv.hr]; exact Nat.mod_le _ _
    have h2 : a.toNat / 2^(j+1) ≤ a.toNat / 2 := Nat.div_le_div_left (by
      have : 2 ≤ 2^(j+1) := by rw [pj]; omega
      exact this) (by decide)
    omega
  have r1Nat : r1.toNat = 2 * r.toNat + (a.toNat / 2^j) % 2 := by
    have := shift_or_bit r ((a >>> j) &&& 1#64) rsmall (by rw [bitEq]; omega)
    rw [bitEq] at this; exact this
  -- decomposition of P'
  have decomp : a.toNat / 2^j = b.toNat * (2 * (a.toNat / 2^(j+1) / b.toNat)) + r1.toNat := by
    have d1 := Nat.div_add_mod (a.toNat / 2^j) 2
    have d2 := Nat.div_add_mod (a.toNat / 2^(j+1)) b.toNat
    rw [r1Nat, inv.hr]
    rw [hP] at d2 ⊢
    rw [Nat.mul_left_comm]
    omega
  have rlt : r.toNat < b.toNat := by rw [inv.hr]; exact Nat.mod_lt _ pos
  have hq2 : q.toNat % 2^(j+1) = 0 := by rw [inv.hq]; exact Nat.mul_mod_left _ _
  constructor
  · intro notLess
    have ge : b.toNat ≤ r1.toNat := by rw [BitVec.lt_def] at notLess; omega
    have sub : (r1 - b).toNat = r1.toNat - b.toNat := BitVec.toNat_sub_of_le (BitVec.le_def.mpr ge)
    have orq := or_pow q j hj hq2
    have uniq := (Nat.div_mod_unique pos (a := a.toNat / 2^j) (d := 2 * (a.toNat / 2^(j+1) / b.toNat) + 1)
      (c := r1.toNat - b.toNat)).mpr ⟨by rw [decomp, Nat.mul_add]; omega, by omega⟩
    refine ⟨pos, by omega, ?_, ?_⟩
    · rw [orq, inv.hq, uniq.1]
      generalize a.toNat / 2^(j+1) / b.toNat = X
      rw [pj]
      simp only [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    · rw [sub, uniq.2]
  · intro less
    have lt : r1.toNat < b.toNat := BitVec.lt_def.mp less
    have uniq := (Nat.div_mod_unique pos (a := a.toNat / 2^j) (d := 2 * (a.toNat / 2^(j+1) / b.toNat))
      (c := r1.toNat)).mpr ⟨by rw [decomp]; omega, lt⟩
    refine ⟨pos, by omega, ?_, ?_⟩
    · rw [inv.hq, uniq.1]
      generalize a.toNat / 2^(j+1) / b.toNat = X
      rw [pj]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    · rw [uniq.2]

theorem udivInv_initial (a b : BitVec 64) (pos : 0 < b.toNat) : UdivInv a b 0 0 64 := by
  have : a.toNat / 2^64 = 0 := Nat.div_eq_of_lt a.isLt
  exact ⟨pos, Nat.le_refl _, by simp [this], by simp [this]⟩

theorem udivInv_final {a b q r : BitVec 64} (inv : UdivInv a b q r 0) :
    q.toNat = a.toNat / b.toNat ∧ r.toNat = a.toNat % b.toNat := by
  have h1 := inv.hq; have h2 := inv.hr
  simp only [Nat.pow_zero, Nat.div_one, Nat.mul_one] at h1 h2
  exact ⟨h1, h2⟩

#print axioms udivInv_step
#print axioms udivInv_initial
#print axioms udivInv_final
end InitECandidate.Runtime
