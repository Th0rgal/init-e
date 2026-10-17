import InitECandidate.Runtime.TypedJournalUndoRecords
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Appending one complete accessible record preserves all earlier undo records. -/
theorem JournalUndoRecords.append {F : Type} {journal : BitVec 64} {count : Nat}
    {before after : PanSemStateFiniteExact 64 F} (valid : JournalUndoRecords journal count before)
    (domain : after.memaddrs = before.memaddrs)
    (frame : ∀ index : Nat, index < count → ∀ offset ∈ ([0,8,16,24] : List Nat),
      after.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) =
        before.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset))
    (table key present value keyLength : BitVec 64)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (tableCell : after.memory (journal + BitVec.ofNat 64 count * 32) = .word table)
    (keyCell : after.memory (journal + BitVec.ofNat 64 count * 32 + 8) = .word key)
    (presentCell : after.memory (journal + BitVec.ofNat 64 count * 32 + 16) = .word present)
    (valueCell : after.memory (journal + BitVec.ofNat 64 count * 32 + 24) = .word value)
    (fields : ∀ offset ∈ ([0,8,16,24] : List Nat), after.memaddrs (journal + BitVec.ofNat 64 count * 32 + BitVec.ofNat 64 offset))
    (aligned : key.toNat % 8 = 0)
    (words : ∀ offset : Nat, offset < keyLength.toNat → after.memaddrs (key + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < keyLength.toNat → after.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    JournalUndoRecords journal (count + 1) after := by
  have prefixValid := valid.after_frame (Nat.le_refl _) domain frame
  intro index inside
  by_cases earlier : index < count
  · exact prefixValid index earlier
  · have same : index = count := by omega
    subst index
    exact ⟨table,key,present,value,keyLength,supported,tableCell,keyCell,presentCell,valueCell,fields,aligned,words,bytes⟩

/-- The appended key is checked against the fixed width of the table actually
stored in the same record, rather than an independently chosen key width. -/
theorem TypedJournalUndoRecords.append {F : Type} {widths : BitVec 64 → BitVec 64}
    {journal : BitVec 64} {count : Nat} {before after : PanSemStateFiniteExact 64 F}
    (valid : TypedJournalUndoRecords widths journal count before)
    (domain : after.memaddrs = before.memaddrs)
    (frame : ∀ index : Nat, index < count → ∀ offset ∈ ([0,8,16,24] : List Nat),
      after.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) =
        before.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset))
    (table key present value : BitVec 64)
    (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (tableCell : after.memory (journal + BitVec.ofNat 64 count * 32) = .word table)
    (keyCell : after.memory (journal + BitVec.ofNat 64 count * 32 + 8) = .word key)
    (presentCell : after.memory (journal + BitVec.ofNat 64 count * 32 + 16) = .word present)
    (valueCell : after.memory (journal + BitVec.ofNat 64 count * 32 + 24) = .word value)
    (fields : ∀ offset ∈ ([0,8,16,24] : List Nat), after.memaddrs (journal + BitVec.ofNat 64 count * 32 + BitVec.ofNat 64 offset))
    (aligned : key.toNat % 8 = 0)
    (words : ∀ offset : Nat, offset < (widths table).toNat → after.memaddrs (key + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < (widths table).toNat → after.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    TypedJournalUndoRecords widths journal (count + 1) after := by
  have prefixValid := valid.after_frame (Nat.le_refl _) domain frame
  refine ⟨valid.1.append domain frame table key present value (widths table) supported tableCell keyCell presentCell valueCell fields aligned words bytes,?_⟩
  intro index inside actualTable actualKey actualTableCell actualKeyCell
  by_cases earlier : index < count
  · exact prefixValid.2 index earlier actualTable actualKey actualTableCell actualKeyCell
  · have same : index = count := by omega
    subst index
    have tableSame : actualTable = table := HolWordLab.word.inj (actualTableCell.symm.trans tableCell)
    have keySame : actualKey = key := HolWordLab.word.inj (actualKeyCell.symm.trans keyCell)
    subst actualTable
    subst actualKey
    exact ⟨supported,words,bytes⟩

#print axioms JournalUndoRecords.append
#print axioms TypedJournalUndoRecords.append
end InitECandidate.Runtime
