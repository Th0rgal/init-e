import InitECandidate.Runtime.JournalRecordStoreFrames
import InitECandidate.Runtime.HashTableReadyJournal32
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Saving a complete next record leaves every earlier live field unchanged. -/
theorem journalRecordPost32_prefix_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (journal record table key present value : BitVec 64) (count : Nat)
    (bounded : journal.toNat + count * 32 ≤ 33806089496)
    (recordBound : record.toNat + 32 ≤ 33806089496)
    (afterPrefix : journal.toNat + count * 32 ≤ record.toNat) :
    ∀ index : Nat, index < count → ∀ offset ∈ ([0,8,16,24] : List Nat),
      (journalRecordPost32 state record table key present value).memory
        (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) =
      state.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) := by
  have later : ∀ offset : Nat, offset < 32 → journal.toNat + count * 32 ≤ (record + BitVec.ofNat 64 offset).toNat := by
    intro offset small
    have natural : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    omega
  have first := journal_record_word_frame state journal record table count bounded (Or.inr afterPrefix)
  have second := journal_record_word_frame (sourceWriteWord state record table) journal (record + 8) key count bounded (Or.inr (later 8 (by decide)))
  have third := journal_record_word_frame (sourceWriteWord (sourceWriteWord state record table) (record + 8) key) journal (record + 16) present count bounded (Or.inr (later 16 (by decide)))
  have fourth := journal_record_word_frame (sourceWriteWord (sourceWriteWord (sourceWriteWord state record table) (record + 8) key) (record + 16) present) journal (record + 24) value count bounded (Or.inr (later 24 (by decide)))
  intro index inside offset member
  exact (fourth index inside offset member).trans ((third index inside offset member).trans ((second index inside offset member).trans (first index inside offset member)))

/-- Readback of all four fields saved by the original record stores. -/
theorem journalRecordPost32_fields {F : Type} (state : PanSemStateFiniteExact 64 F)
    (record table key present value : BitVec 64) :
    (journalRecordPost32 state record table key present value).memory record = .word table ∧
    (journalRecordPost32 state record table key present value).memory (record + 8) = .word key ∧
    (journalRecordPost32 state record table key present value).memory (record + 16) = .word present ∧
    (journalRecordPost32 state record table key present value).memory (record + 24) = .word value := by
  simp [journalRecordPost32,sourceWriteWord]

#print axioms journalRecordPost32_prefix_frame
#print axioms journalRecordPost32_fields
end InitECandidate.Runtime
