import InitECandidate.Runtime.HashTableReadyJournal32
import InitECandidate.Runtime.HashTableReadyWordOutside
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Journal records may name a different table from the one being preserved. -/
theorem HashTableReady.journal_record_other {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items record savedTable savedKey present value : BitVec 64) (bits : Nat)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (bounded : record.toNat + 32 ≤ 33806089496)
    (outside : record.toNat + 32 ≤ table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ record.toNat) :
    HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer
      (journalRecordPost32 state record savedTable savedKey present value) := by
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
  have one := ready.after_word_outside state keyLength table pointer keys stride capacity used values order orderPos items record savedTable bits zero
  have two := one.after_word_outside _ keyLength table pointer keys stride capacity used values order orderPos items (record + 8) savedKey bits (separation 8 (by decide))
  have three := two.after_word_outside _ keyLength table pointer keys stride capacity used values order orderPos items (record + 16) present bits (separation 16 (by decide))
  exact three.after_word_outside _ keyLength table pointer keys stride capacity used values order orderPos items (record + 24) value bits (separation 24 (by decide))


#print axioms HashTableReady.journal_record_other
end InitECandidate.Runtime
