import InitECandidate.Runtime.StatelessMidRun
import InitECandidate.Runtime.SszSplitCellsStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem notLt_toNat (a b : BitVec 64) (h : ¬ a < b) : b.toNat ≤ a.toNat := by
  rw [BitVec.lt_def] at h; omega

theorem sszOffsetOK_k {σ : Type} (st : PanSemStateFiniteExact 64 σ) (offs fixed len k : BitVec 64)
    (pos : k ≠ 0) (small : k.toNat < 2 ^ 63) (h : SszOffsetOK st offs fixed len k) :
    fixed.toNat ≤ (memWord st.memory (offs + k * 8)).toNat ∧ (memWord st.memory (offs + k * 8)).toNat ≤ len.toNat ∧
      (memWord st.memory (offs + k * 8 - 8)).toNat ≤ (memWord st.memory (offs + k * 8)).toNat := by
  obtain ⟨_, a, b, c⟩ := h
  have p := (sszPos_iff k small).mpr pos
  exact ⟨notLt_toNat _ _ a, notLt_toNat _ _ b, notLt_toNat _ _ (c p).2⟩

/-- Two accepted offsets with fixed part 16: o0 = 16 ≤ o1 ≤ len. -/
theorem check2_geometry {σ : Type} (st : PanSemStateFiniteExact 64 σ) (offs len : BitVec 64)
    (h : SszCheckOffsetsReturned st offs 2 16 len (.val (.word 0))) :
    memWord st.memory offs = 16 ∧ 16 ≤ (memWord st.memory (offs + 8)).toNat ∧
      (memWord st.memory (offs + 8)).toNat ≤ len.toNat := by
  obtain ⟨_, all, first⟩ := h
  have k1 := sszOffsetOK_k st offs 16 len 1 (by decide) (by decide) (all 1 (by decide))
  simp only [show (1 : BitVec 64) * 8 = 8 from rfl, show offs + 8 - 8 = offs by simp] at k1
  exact ⟨(first (by decide)).2, by simpa using k1.1, k1.2.1⟩

/-- Three accepted offsets with fixed part 44: o0 = 44 ≤ o1 ≤ o2 ≤ len. -/
theorem check3_geometry {σ : Type} (st : PanSemStateFiniteExact 64 σ) (offs len : BitVec 64)
    (h : SszCheckOffsetsReturned st offs 3 44 len (.val (.word 0))) :
    memWord st.memory offs = 44 ∧ 44 ≤ (memWord st.memory (offs + 8)).toNat ∧
      (memWord st.memory (offs + 8)).toNat ≤ (memWord st.memory (offs + 16)).toNat ∧
      (memWord st.memory (offs + 16)).toNat ≤ len.toNat := by
  obtain ⟨_, all, first⟩ := h
  have k1 := sszOffsetOK_k st offs 44 len 1 (by decide) (by decide) (all 1 (by decide))
  have k2 := sszOffsetOK_k st offs 44 len 2 (by decide) (by decide) (all 2 (by decide))
  simp only [show (1 : BitVec 64) * 8 = 8 from rfl, show (2 : BitVec 64) * 8 = 16 from rfl,
    show offs + 8 - 8 = offs by simp, show offs + 16 - 8 = offs + 8 by
      rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl] at k1 k2
  exact ⟨(first (by decide)).2, by simpa using k1.1, k2.2.2, k2.2.1⟩

#print axioms check3_geometry
end InitECandidate.Runtime
