import InitECandidate.Runtime.JournalUndoRecordStores
import InitECandidate.Runtime.JournalRecordGeometry32
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Live journal field addresses remain inside their allocation without wrapping. -/
theorem journal_undo_field_interval (journal : BitVec 64) (count index offset : Nat)
    (bounded : journal.toNat + count * 32 ≤ 33806089496)
    (inside : index < count) (field : offset < 32) :
    journal.toNat ≤ (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset).toNat ∧
      (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset).toNat < journal.toNat + count * 32 := by
  have indexBound : index < 2 ^ 64 := by omega
  have indexNat : (BitVec.ofNat 64 index).toNat = index := Nat.mod_eq_of_lt indexBound
  have productNat : (BitVec.ofNat 64 index * (32 : BitVec 64)).toNat = index * 32 := by
    rw [BitVec.toNat_mul_of_lt (by rw [indexNat]; change index * 32 < 2 ^ 64; omega)]
    rw [indexNat]
    rfl
  have recordNat : (journal + BitVec.ofNat 64 index * (32 : BitVec 64)).toNat = journal.toNat + index * 32 := by
    rw [BitVec.toNat_add_of_lt (by rw [productNat]; omega),productNat]
  have offsetNat : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
  have address : (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset).toNat = journal.toNat + index * 32 + offset := by
    rw [BitVec.toNat_add_of_lt (by rw [recordNat,offsetNat]; omega),recordNat,offsetNat]
  omega

/-- A word outside the journal allocation cannot overwrite any live field. -/
theorem JournalUndoRecords.after_word_interval {F : Type} {journal : BitVec 64} {count : Nat}
    (state : PanSemStateFiniteExact 64 F) (address value : BitVec 64)
    (valid : JournalUndoRecords journal count state)
    (bounded : journal.toNat + count * 32 ≤ 33806089496)
    (outside : address.toNat < journal.toNat ∨ journal.toNat + count * 32 ≤ address.toNat) :
    JournalUndoRecords journal count (sourceWriteWord state address value) := by
  apply valid.after_word state address value
  intro index inside offset member equal
  have small : offset < 32 := by simp at member; omega
  have interval := journal_undo_field_interval journal count index offset bounded inside small
  rw [equal] at interval
  rcases outside with before | after <;> omega

/-- An occupancy store in an array disjoint from the journal preserves all records,
including when the byte address lies inside its aligned containing word. -/
theorem JournalUndoRecords.after_array_byte {F : Type} {journal : BitVec 64} {count : Nat}
    (state : PanSemStateFiniteExact 64 F) (base length index value cell : BitVec 64)
    (valid : JournalUndoRecords journal count state)
    (journalBound : journal.toNat + count * 32 ≤ 33806089496)
    (inside : index.toNat < length.toNat) (aligned : base.toNat % 8 = 0)
    (bounded : base.toNat + length.toNat ≤ 2 ^ 64)
    (separate : base.toNat + length.toNat ≤ journal.toNat ∨ journal.toNat + count * 32 ≤ base.toNat) :
    JournalUndoRecords journal count (sourceWriteByte state (base + index) value cell) := by
  have interval := hashOccupancy_aligned_interval base length index aligned bounded inside
  apply valid.after_word_interval state (panByteAlignHOL (base + index)) _ journalBound
  rcases separate with before | after
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- Concrete deletion occupancy clear framed by allocation separation alone. -/
theorem evaluate_hashDelete_clear_journal_interval {F : Type} (state : PanSemStateFiniteExact 64 F)
    (journal base length hole cell : BitVec 64) (count : Nat)
    (valid : JournalUndoRecords journal count state)
    (journalBound : journal.toNat + count * 32 ≤ 33806089496)
    (inside : hole.toNat < length.toNat) (aligned : base.toNat % 8 = 0)
    (bounded : base.toNat + length.toNat ≤ 2 ^ 64)
    (separate : base.toNat + length.toNat ≤ journal.toNat ∨ journal.toNat + count * 32 ≤ base.toNat)
    (usedLocal : state.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "used") = some (.val (.word base)))
    (holeLocal : state.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "i") = some (.val (.word hole)))
    (domain : state.memaddrs (panByteAlignHOL (base + hole)))
    (memory : state.memory (panByteAlignHOL (base + hole)) = .word cell) :
    ∃ post, evaluateHOLFiniteState state hashDeleteClear = (none,post) ∧ JournalUndoRecords journal count post := by
  exact ⟨sourceWriteByte state (base + hole) 0 cell,
    (evaluate_hashDelete_clear state base hole cell usedLocal holeLocal domain memory).1,
    valid.after_array_byte state base length hole 0 cell journalBound inside aligned bounded separate⟩

#print axioms evaluate_hashDelete_clear_journal_interval
#print axioms journal_undo_field_interval
#print axioms JournalUndoRecords.after_word_interval
#print axioms JournalUndoRecords.after_array_byte
end InitECandidate.Runtime
