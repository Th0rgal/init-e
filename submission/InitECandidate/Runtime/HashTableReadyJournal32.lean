import InitECandidate.Runtime.HashTableReadyWordOutside32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The four word updates used to save a journal record. -/
noncomputable def journalRecordPost32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (record table key present value : BitVec 64) : PanSemStateFiniteExact 64 F :=
  sourceWriteWord (sourceWriteWord (sourceWriteWord (sourceWriteWord state record table)
    (record + 8) key) (record + 16) present) (record + 24) value

/-- A complete journal record outside a table preserves the mixed-operation
invariant; its four stores require no source clock. -/
theorem HashTableReady32.journal_record {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items record savedKey present value : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (bounded : record.toNat + 32 ≤ 33806089496)
    (outside : record.toNat + 32 ≤ table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ record.toNat) :
    HashTableReady32 table keys stride capacity used values order orderPos items bits pointer
      (journalRecordPost32 state record table savedKey present value) := by
  have separation : ∀ offset : Nat, offset < 32 →
      (record + BitVec.ofNat 64 offset).toNat < table.toNat ∨
        orderPos.toNat + capacity.toNat * 8 ≤ (record + BitVec.ofNat 64 offset).toNat := by
    intro offset inside
    have natural : (BitVec.ofNat 64 offset).toNat = offset := by
      change offset % 2 ^ 64 = offset
      exact Nat.mod_eq_of_lt (by omega)
    have address : (record + BitVec.ofNat 64 offset).toNat = record.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    rcases outside with before | after
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have zero : record.toNat < table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ record.toNat := by
    simpa using separation 0 (by decide)
  have one := ready.after_word_outside state table pointer keys stride capacity used values order orderPos items record table bits zero
  have two := one.after_word_outside _ table pointer keys stride capacity used values order orderPos items (record + 8) savedKey bits (separation 8 (by decide))
  have three := two.after_word_outside _ table pointer keys stride capacity used values order orderPos items (record + 16) present bits (separation 16 (by decide))
  exact three.after_word_outside _ table pointer keys stride capacity used values order orderPos items (record + 24) value bits (separation 24 (by decide))

/-- Actual word-store execution for a normalized journal record. -/
theorem evaluate_journal_record32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (record table key present value : BitVec 64)
    (domain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (record + BitVec.ofNat 64 offset)) :
    evaluateHOLFiniteState state
      (.seq (.store (.const record) (.const table))
        (.seq (.store (.const (record + 8)) (.const key))
          (.seq (.store (.const (record + 16)) (.const present))
            (.store (.const (record + 24)) (.const value))))) =
      (none,journalRecordPost32 state record table key present value) := by
  have first := evaluate_store_word state record table (.const record) (.const table)
    (by simp [evalHOLExact]) (by simp [evalHOLExact]) (by simpa using domain 0 (by simp))
  have second := evaluate_store_word (sourceWriteWord state record table) (record + 8) key (.const (record + 8)) (.const key)
    (by simp [evalHOLExact]) (by simp [evalHOLExact]) (domain 8 (by simp))
  have third := evaluate_store_word (sourceWriteWord (sourceWriteWord state record table) (record + 8) key)
    (record + 16) present (.const (record + 16)) (.const present)
    (by simp [evalHOLExact]) (by simp [evalHOLExact]) (domain 16 (by simp))
  have fourth := evaluate_store_word (sourceWriteWord (sourceWriteWord (sourceWriteWord state record table) (record + 8) key) (record + 16) present)
    (record + 24) value (.const (record + 24)) (.const value)
    (by simp [evalHOLExact]) (by simp [evalHOLExact]) (domain 24 (by simp))
  exact evaluate_seq_none first (evaluate_seq_none second (evaluate_seq_none third fourth))

#print axioms HashTableReady32.journal_record
#print axioms evaluate_journal_record32
end InitECandidate.Runtime
