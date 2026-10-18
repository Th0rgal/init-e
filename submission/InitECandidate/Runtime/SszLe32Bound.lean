import InitECandidate.Runtime.SszSplitVarListSource
import InitECandidate.Runtime.SszCheckOffsetsChecks
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section
variable {σ : Type} (st : PanSemStateExact 64 σ) [DecidablePred st.memaddrs]

theorem eval_loadByte_lt (a : ExpHOL 64) (v : ValueHOL 64) (h : evalHOLExact st (.loadByte a) = some v) :
    ∃ x : BitVec 64, v = .val (.word x) ∧ x.toNat < 2 ^ 8 := by
  simp only [evalHOLExact] at h
  split at h
  · cases hb : panMemLoadByteHOL st.memory st.memaddrs st.be _ with
    | none => rw [hb] at h; simp at h
    | some b =>
      rw [hb] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      refine ⟨_, rfl, ?_⟩
      have := b.toNat_lt
      rw [BitVec.toNat_ofNat]
      omega
  · simp at h

theorem eval_shift8_lt (a : ExpHOL 64) (k : Nat) (hk : k ≤ 24) (v : ValueHOL 64)
    (h : evalHOLExact st (.shift .lsl (.loadByte a) (.const (BitVec.ofNat 64 k))) = some v) :
    ∃ x : BitVec 64, v = .val (.word x) ∧ x.toNat < 2 ^ (8 + k) := by
  cases hb : evalHOLExact st (.loadByte a) with
  | none => rw [evalHOLExact, hb] at h; simp at h
  | some x =>
    obtain ⟨y, rfl, hy⟩ := eval_loadByte_lt st a x hb
    have hk64 : (BitVec.ofNat 64 k).toNat = k := by rw [BitVec.toNat_ofNat]; omega
    rw [evalHOLExact, hb] at h
    simp only [evalHOLExact, hk64, wordShiftHOL] at h
    have notBig : ¬ (k ≠ 0 ∧ 64 ≤ k) := by omega
    simp only [notBig, if_false, Option.map_some, Option.some.injEq] at h
    subst h
    refine ⟨_, rfl, ?_⟩
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have lt : y.toNat * 2 ^ k < 2 ^ (8 + k) := by
      rw [Nat.pow_add]; exact Nat.mul_lt_mul_of_pos_right hy (Nat.two_pow_pos k)
    have le : 2 ^ (8 + k) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.mod_eq_of_lt (by omega)]
    exact lt

def Bounded32 (e : ExpHOL 64) : Prop :=
  ∀ v, evalHOLExact st e = some v → ∃ x : BitVec 64, v = .val (.word x) ∧ x.toNat < 2 ^ 32

theorem bounded32_or4 (e0 e1 e2 e3 : ExpHOL 64) (b0 : Bounded32 st e0) (b1 : Bounded32 st e1)
    (b2 : Bounded32 st e2) (b3 : Bounded32 st e3) : Bounded32 st (.op .or [e0, e1, e2, e3]) := by
  intro v h
  rw [evalHOLExact] at h
  cases h0 : evalHOLExact st e0 with
  | none => simp [evalListHOLExact, h0] at h
  | some v0 =>
  cases h1 : evalHOLExact st e1 with
  | none => simp [evalListHOLExact, h0, h1] at h
  | some v1 =>
  cases h2 : evalHOLExact st e2 with
  | none => simp [evalListHOLExact, h0, h1, h2] at h
  | some v2 =>
  cases h3 : evalHOLExact st e3 with
  | none => simp [evalListHOLExact, h0, h1, h2, h3] at h
  | some v3 =>
  obtain ⟨x0, rfl, l0⟩ := b0 _ h0
  obtain ⟨x1, rfl, l1⟩ := b1 _ h1
  obtain ⟨x2, rfl, l2⟩ := b2 _ h2
  obtain ⟨x3, rfl, l3⟩ := b3 _ h3
  simp [evalListHOLExact, h0, h1, h2, h3, valueIsWord, valueWord, wordOpHOL, wordOp, orop_eq] at h
  subst h
  refine ⟨_, rfl, ?_⟩
  simp only [BitVec.toNat_or]
  exact Nat.or_lt_two_pow l0 (Nat.or_lt_two_pow l1 (Nat.or_lt_two_pow l2 l3))

theorem bounded32_loadByte (a : ExpHOL 64) : Bounded32 st (.loadByte a) := by
  intro v h
  obtain ⟨x, rfl, l⟩ := eval_loadByte_lt st a v h
  exact ⟨x, rfl, by omega⟩

theorem bounded32_shift (a : ExpHOL 64) (k : Nat) (hk : k ≤ 24) :
    Bounded32 st (.shift .lsl (.loadByte a) (.const (BitVec.ofNat 64 k))) := by
  intro v h
  obtain ⟨x, rfl, l⟩ := eval_shift8_lt st a k hk v h
  have : 2 ^ (8 + k) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
  exact ⟨x, rfl, by omega⟩

/-- Both little-endian 32-bit reads of ssz_split_var_list are below 2^32. -/
theorem sszSplitFirst_bounded : Bounded32 st sszSplitFirst :=
  bounded32_or4 st _ _ _ _ (bounded32_loadByte st _) (bounded32_shift st _ 8 (by decide))
    (bounded32_shift st _ 16 (by decide)) (bounded32_shift st _ 24 (by decide))

theorem sszSplitOffsetAt_bounded : Bounded32 st sszSplitOffsetAt :=
  bounded32_or4 st _ _ _ _ (bounded32_loadByte st _) (bounded32_shift st _ 8 (by decide))
    (bounded32_shift st _ 16 (by decide)) (bounded32_shift st _ 24 (by decide))

end

#print axioms sszSplitFirst_bounded
#print axioms sszSplitOffsetAt_bounded
end InitECandidate.Runtime
