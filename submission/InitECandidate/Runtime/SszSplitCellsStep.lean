import InitECandidate.Runtime.SszSplitCells
namespace InitECandidate.Runtime
open Flapjack

abbrev SszMem := BitVec 64 → HolWordLab 64

/-- Slice cells written for indices below i, their offset checks, and the frame. -/
def SszSplitCellsOK (m0 : SszMem) (dom : BitVec 64 → Prop) (p len first arr : BitVec 64)
    (off : BitVec 64 → BitVec 64) (i : BitVec 64) (M : SszMem) : Prop :=
  (∀ k : BitVec 64, k.toNat < i.toNat → ¬ off k < first ∧ ¬ len < off k ∧ dom (arr + k * 16) ∧
    M (arr + k * 16) = .word (p + off k)) ∧
  (∀ k : BitVec 64, k.toNat + 1 < i.toNat → ¬ off (k + 1) < off k ∧ dom (arr + k * 16 + 8) ∧
    M (arr + k * 16 + 8) = .word (off (k + 1) - off k)) ∧
  (∀ a, (∀ k : BitVec 64, k.toNat < i.toNat → a ≠ arr + k * 16 ∧ a ≠ arr + k * 16 + 8) → M a = m0 a)

theorem sszPos_iff (i : BitVec 64) (h : i.toNat < 2 ^ 63) :
    Flapjack.Compiler.Encoders.Asm.holAsmSignedLess 0#64 i = true ↔ i ≠ 0 := by
  unfold Flapjack.Compiler.Encoders.Asm.holAsmSignedLess
  have : i ≠ 0 ↔ 0 < i.toNat := by
    constructor
    · intro ne; apply Nat.pos_of_ne_zero; intro z; exact ne (BitVec.eq_of_toNat_eq (by simp [z]))
    · intro pos e; subst e; simp at pos
  rw [this]
  simp only [BitVec.toNat_ofNat]
  constructor
  · intro hh; simp at hh; omega
  · intro hh; simp; omega

theorem sszSplitCells_initial (m0 : SszMem) (dom : BitVec 64 → Prop) (p len first arr : BitVec 64)
    (off : BitVec 64 → BitVec 64) : SszSplitCellsOK m0 dom p len first arr off 0 m0 :=
  ⟨fun k h => by simp at h, fun k h => by simp at h, fun _ _ => rfl⟩

theorem sszSplitCells_step (m0 M : SszMem) (dom : BitVec 64 → Prop) (p len first arr i prev o count : BitVec 64)
    (off : BitVec 64 → BitVec 64) (hi : i.toNat < count.toNat) (hc : count.toNat < 2 ^ 60)
    (cells : SszSplitCellsOK m0 dom p len first arr off i M) (hprev : i ≠ 0 → prev = off (i - 1))
    (o1 : ¬ o < first) (o2 : ¬ len < o) (o3 : ¬ o < prev)
    (d1 : Flapjack.Compiler.Encoders.Asm.holAsmSignedLess 0#64 i = true → dom (arr + (i - 1) * 16 + 8))
    (d2 : dom (arr + i * 16)) :
    SszSplitCellsOK m0 dom p len first arr (fun k => if k = i then o else off k) (i + 1)
      (sszSplitStepMemory M arr p i o prev) := by
  obtain ⟨c0, c8, frame⟩ := cells
  have succ : (i + 1).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  have iSmall : i.toNat < 2 ^ 60 := by omega
  have pos := sszPos_iff i (by omega)
  have predNat : i ≠ 0 → (i - 1).toNat = i.toNat - 1 := by
    intro ne
    have : 0 < i.toNat := Nat.pos_of_ne_zero (fun z => ne (BitVec.eq_of_toNat_eq (by simp [z])))
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
  unfold SszSplitCellsOK sszSplitStepMemory
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    rw [succ] at hk
    by_cases eq : k = i
    · subst eq
      exact ⟨by simpa using o1, by simpa using o2, d2, by simp [wmem]⟩
    · have lt : k.toNat < i.toNat := by
        have : k.toNat ≠ i.toNat := fun h => eq (BitVec.eq_of_toNat_eq h)
        omega
      obtain ⟨a, b, c, d⟩ := c0 k lt
      simp only [if_neg eq]
      refine ⟨a, b, c, ?_⟩
      have n2 : arr + k * 16 ≠ arr + i * 16 := sszCell_ptr_ne arr k i (by omega) iSmall eq
      simp only [wmem, if_neg n2]
      split
      · rename_i positive
        have ne := (pos.mp positive)
        have n1 : arr + k * 16 ≠ arr + (i - 1) * 16 + 8 :=
          fun h => sszCell_len_ne_ptr arr (i - 1) k (by rw [predNat ne]; omega) (by omega) h.symm
        simp only [wmem, if_neg n1]; exact d
      · exact d
  · intro k hk
    rw [succ] at hk
    by_cases last : k.toNat + 1 = i.toNat
    · have ne : i ≠ 0 := fun z => by subst z; simp at last
      have keq : k = i - 1 := BitVec.eq_of_toNat_eq (by rw [predNat ne]; omega)
      subst keq
      have kp1 : i - 1 + 1 = i := by simp
      have kne : i - 1 ≠ i := fun h => by
        have := congrArg BitVec.toNat h; rw [predNat ne] at this; omega
      have n12 : arr + (i - 1) * 16 + 8 ≠ arr + i * 16 :=
        sszCell_len_ne_ptr arr (i - 1) i (by rw [predNat ne]; omega) iSmall
      have positive := pos.mpr ne
      rw [kp1]
      simp only [if_pos rfl, if_neg kne]
      rw [← hprev ne]
      refine ⟨o3, d1 positive, ?_⟩
      simp only [wmem, if_neg n12, positive, if_true]
    · have lt : k.toNat + 1 < i.toNat := by omega
      obtain ⟨a, b, c⟩ := c8 k lt
      have kne : k ≠ i := fun h => by subst h; omega
      have k1 : (k + 1).toNat = k.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
      have k1ne : k + 1 ≠ i := fun h => by have := congrArg BitVec.toNat h; omega
      simp only [if_neg kne, if_neg k1ne]
      refine ⟨a, b, ?_⟩
      have n2 : arr + k * 16 + 8 ≠ arr + i * 16 := sszCell_len_ne_ptr arr k i (by omega) iSmall
      simp only [wmem, if_neg n2]
      split
      · rename_i positive
        have ne := pos.mp positive
        have kne1 : k ≠ i - 1 := fun h => by
          have := congrArg BitVec.toNat h; rw [predNat ne] at this; omega
        have n1 : arr + k * 16 + 8 ≠ arr + (i - 1) * 16 + 8 :=
          sszCell_len_ne arr k (i - 1) (by omega) (by rw [predNat ne]; omega) kne1
        simp only [wmem, if_neg n1]; exact c
      · exact c
  · intro a ex
    have e2 := (ex i (by omega)).1
    simp only [wmem, if_neg e2]
    split
    · rename_i positive
      have ne := pos.mp positive
      have e1 := (ex (i - 1) (by rw [predNat ne]; omega)).2
      simp only [wmem, if_neg e1]
      exact frame a (fun k hk => ex k (by omega))
    · exact frame a (fun k hk => ex k (by omega))

#print axioms sszSplitCells_step

end InitECandidate.Runtime
