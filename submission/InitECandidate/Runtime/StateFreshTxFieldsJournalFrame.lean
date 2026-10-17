import InitECandidate.Runtime.StateFreshTxFieldsRecordFrame
import InitECandidate.Runtime.JournalRecordAppendFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A journal record before the transaction header cannot change its eight
table pointers. This applies to both original journal mutation routines. -/
theorem StateFreshTxFields.after_journal_record {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (ts fieldPointer record table key present value : BitVec 64)
    (fields : StateFreshTxFields ts fieldPointer stateFreshTxAllTables state)
    (tsBound : ts.toNat + 72 ≤ 33806089496)
    (recordBefore : record.toNat + 32 ≤ ts.toNat) :
    StateFreshTxFields ts fieldPointer stateFreshTxAllTables
      (journalRecordPost32 state record table key present value) := by
  have start : (ts + (8 : BitVec 64)).toNat = ts.toNat + 8 := by
    rw [BitVec.toNat_add_of_lt (by change ts.toNat + 8 < 2 ^ 64; omega)]
    rfl
  have bounded : (ts + (8 : BitVec 64)).toNat + 2 * 32 ≤ 33806089496 := by omega
  have later : ∀ offset : Nat, offset ≤ 24 →
      (record + BitVec.ofNat 64 offset).toNat < (ts + (8 : BitVec 64)).toNat := by
    intro offset small
    have natural : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    omega
  have first := journal_record_word_frame state (ts + 8) record table 2 bounded (Or.inl (by simpa using later 0 (by decide)))
  have second := journal_record_word_frame (sourceWriteWord state record table) (ts + 8) (record + 8) key 2 bounded (Or.inl (by simpa using later 8 (by decide)))
  have third := journal_record_word_frame (sourceWriteWord (sourceWriteWord state record table) (record + 8) key) (ts + 8) (record + 16) present 2 bounded (Or.inl (by simpa using later 16 (by decide)))
  have fourth := journal_record_word_frame (sourceWriteWord (sourceWriteWord (sourceWriteWord state record table) (record + 8) key) (record + 16) present) (ts + 8) (record + 24) value 2 bounded (Or.inl (by simpa using later 24 (by decide)))
  apply fields.after_two_record_frame
  intro index inside offset member
  exact (fourth index inside offset member).trans ((third index inside offset member).trans ((second index inside offset member).trans (first index inside offset member)))

#print axioms StateFreshTxFields.after_journal_record
end InitECandidate.Runtime
