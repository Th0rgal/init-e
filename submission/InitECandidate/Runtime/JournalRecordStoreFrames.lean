import InitECandidate.Runtime.JournalUndoRecordIntervals
import InitECandidate.Runtime.HashDeleteFinalStoresJournal
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Exact field contents, including saved table identities, survive a disjoint store. -/
theorem journal_record_word_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (journal address value : BitVec 64) (count : Nat)
    (bounded : journal.toNat + count * 32 ≤ 33806089496)
    (outside : address.toNat < journal.toNat ∨ journal.toNat + count * 32 ≤ address.toNat) :
    ∀ index : Nat, index < count → ∀ offset ∈ ([0,8,16,24] : List Nat),
      (sourceWriteWord state address value).memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) =
        state.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) := by
  intro index inside offset member
  have small : offset < 32 := by simp at member; omega
  have interval := journal_undo_field_interval journal count index offset bounded inside small
  have different : journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset ≠ address := by
    intro equal
    rw [equal] at interval
    rcases outside with before | after <;> omega
  simp only [sourceWriteWord]
  simp
  intro equal
  exact False.elim (different equal)

theorem journal_record_array_word_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (journal base length index value : BitVec 64) (count : Nat)
    (journalBound : journal.toNat + count * 32 ≤ 33806089496)
    (inside : index.toNat < length.toNat) (aligned : base.toNat % 8 = 0)
    (bounded : base.toNat + length.toNat * 8 ≤ 33806089496)
    (separate : base.toNat + length.toNat * 8 ≤ journal.toNat ∨ journal.toNat + count * 32 ≤ base.toNat) :
    ∀ record : Nat, record < count → ∀ offset ∈ ([0,8,16,24] : List Nat),
      (sourceWriteWord state (base + index * 8) value).memory (journal + BitVec.ofNat 64 record * 32 + BitVec.ofNat 64 offset) =
        state.memory (journal + BitVec.ofNat 64 record * 32 + BitVec.ofNat 64 offset) := by
  have address := (hashFind_slot_address base index 8 length inside
    (by change base.toNat + length.toNat * 8 ≤ 33806089496; exact bounded) aligned (by decide)).1
  change (base + index * 8).toNat = base.toNat + index.toNat * 8 at address
  have product := Nat.mul_lt_mul_of_pos_right inside (by decide : 0 < 8)
  apply journal_record_word_frame state journal (base + index * 8) value count journalBound
  rcases separate with before | after
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem journal_record_array_byte_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (journal base length index value cell : BitVec 64) (count : Nat)
    (journalBound : journal.toNat + count * 32 ≤ 33806089496)
    (inside : index.toNat < length.toNat) (aligned : base.toNat % 8 = 0)
    (bounded : base.toNat + length.toNat ≤ 2 ^ 64)
    (separate : base.toNat + length.toNat ≤ journal.toNat ∨ journal.toNat + count * 32 ≤ base.toNat) :
    ∀ record : Nat, record < count → ∀ offset ∈ ([0,8,16,24] : List Nat),
      (sourceWriteByte state (base + index) value cell).memory (journal + BitVec.ofNat 64 record * 32 + BitVec.ofNat 64 offset) =
        state.memory (journal + BitVec.ofNat 64 record * 32 + BitVec.ofNat 64 offset) := by
  have interval := hashOccupancy_aligned_interval base length index aligned bounded inside
  apply journal_record_word_frame state journal (panByteAlignHOL (base + index)) _ count journalBound
  rcases separate with before | after
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

#print axioms journal_record_word_frame
#print axioms journal_record_array_word_frame
#print axioms journal_record_array_byte_frame
end InitECandidate.Runtime
