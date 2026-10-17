import InitECandidate.Runtime.HashTableValuesInJournalRecord
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Four words beyond the live table footprint preserve all registered values. -/
theorem HashTableValuesIn.journal_record_after {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count record a b c d : BitVec 64) (bits : Nat)
    (arrays : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (targets : Set (BitVec 64)) (entries : HashTableValuesIn table targets state)
    (bounded : record.toNat + 32 ≤ 33806089496)
    (later : orderPos.toNat + capacity.toNat * 8 ≤ record.toNat) :
    HashTableValuesIn table targets (journalRecordPost32 state record a b c d) := by
  have hk := arrays.headerKeys
  have ku := arrays.keysBefore
  have vu := arrays.valuesBefore
  have uo := arrays.usedBefore
  have oo := arrays.orderBefore
  have separate (offset : Nat) (small : offset < 32) :
      ∀ address : BitVec 64, tablePhysicalRegion table keys stride capacity used values order orderPos address →
        address ≠ record + BitVec.ofNat 64 offset := by
    intro address inside same
    have natural : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
    have location : (record + BitVec.ofNat 64 offset).toNat = record.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    rw [same] at inside
    unfold tablePhysicalRegion at inside
    omega
  apply entries.physical_frame state _ keyLength table keys stride capacity used values order orderPos count bits arrays targets
  · intro address inside
    have zero : address ≠ record := by simpa using separate 0 (by decide) address inside
    have eight : address ≠ record + (8 : BitVec 64) := separate 8 (by decide) address inside
    have sixteen : address ≠ record + (16 : BitVec 64) := separate 16 (by decide) address inside
    have twentyFour : address ≠ record + (24 : BitVec 64) := separate 24 (by decide) address inside
    simp only [journalRecordPost32,sourceWriteWord,if_neg zero,if_neg eight,if_neg sixteen,if_neg twentyFour]
  · rfl
  · rfl

#print axioms HashTableValuesIn.journal_record_after
end InitECandidate.Runtime
