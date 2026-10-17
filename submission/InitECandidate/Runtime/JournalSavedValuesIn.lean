import InitECandidate.Runtime.TypedJournalUndoRecords
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A live undo record for a pointer-valued table may only restore a registered
value. Absent-key records and records for numeric-valued tables are unrestricted. -/
def JournalSavedValuesIn {F : Type} (journal : BitVec 64) (count : Nat)
    (watched targets : Set (BitVec 64)) (state : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ index : Nat, index < count → ∀ table present value : BitVec 64,
    state.memory (journal + BitVec.ofNat 64 index * 32) = .word table →
    state.memory (journal + BitVec.ofNat 64 index * 32 + 16) = .word present →
    state.memory (journal + BitVec.ofNat 64 index * 32 + 24) = .word value →
    table ∈ watched → present ≠ 0 → value ∈ targets

theorem JournalSavedValuesIn.empty {F : Type} (journal : BitVec 64)
    (watched targets : Set (BitVec 64)) (state : PanSemStateFiniteExact 64 F) :
    JournalSavedValuesIn journal 0 watched targets state := by
  intro index inside
  omega

theorem JournalSavedValuesIn.shrink {F : Type} {journal : BitVec 64} {count remaining : Nat}
    {watched targets : Set (BitVec 64)} {state : PanSemStateFiniteExact 64 F}
    (valid : JournalSavedValuesIn journal count watched targets state) (bound : remaining ≤ count) :
    JournalSavedValuesIn journal remaining watched targets state := by
  intro index inside
  exact valid index (by omega)

theorem JournalSavedValuesIn.after_frame {F : Type} {journal : BitVec 64} {count remaining : Nat}
    {watched targets : Set (BitVec 64)} {before after : PanSemStateFiniteExact 64 F}
    (valid : JournalSavedValuesIn journal count watched targets before) (bound : remaining ≤ count)
    (frame : ∀ index : Nat, index < remaining → ∀ offset ∈ ([0,16,24] : List Nat),
      after.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) =
        before.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset)) :
    JournalSavedValuesIn journal remaining watched targets after := by
  intro index inside table present value t p v belongs occupied
  have oldTable : before.memory (journal + BitVec.ofNat 64 index * 32) = .word table := by
    simpa using (frame index inside 0 (by simp)).symm.trans (by simpa using t)
  exact valid index (by omega) table present value oldTable
    ((frame index inside 16 (by simp)).symm.trans p) ((frame index inside 24 (by simp)).symm.trans v) belongs occupied

/-- Append the exact table, presence bit, and saved value read by jset. -/
theorem JournalSavedValuesIn.append {F : Type} {journal : BitVec 64} {count : Nat}
    {watched targets : Set (BitVec 64)} {before after : PanSemStateFiniteExact 64 F}
    (valid : JournalSavedValuesIn journal count watched targets before)
    (frame : ∀ index : Nat, index < count → ∀ offset ∈ ([0,16,24] : List Nat),
      after.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) =
        before.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset))
    (table present value : BitVec 64)
    (t : after.memory (journal + BitVec.ofNat 64 count * 32) = .word table)
    (p : after.memory (journal + BitVec.ofNat 64 count * 32 + 16) = .word present)
    (v : after.memory (journal + BitVec.ofNat 64 count * 32 + 24) = .word value)
    (registered : table ∈ watched → present ≠ 0 → value ∈ targets) :
    JournalSavedValuesIn journal (count + 1) watched targets after := by
  have earlier := valid.after_frame (Nat.le_refl _) frame
  intro index inside actualTable actualPresent actualValue actualTableCell ap av belongs occupied
  by_cases old : index < count
  · exact earlier index old actualTable actualPresent actualValue actualTableCell ap av belongs occupied
  · have same : index = count := by omega
    subst index
    have tableSame : actualTable = table := HolWordLab.word.inj (actualTableCell.symm.trans t)
    have presentSame : actualPresent = present := HolWordLab.word.inj (ap.symm.trans p)
    have valueSame : actualValue = value := HolWordLab.word.inj (av.symm.trans v)
    subst actualTable
    subst actualPresent
    subst actualValue
    exact registered belongs occupied

/-- Select a complete typed record together with the registered saved value
needed by the actual restore-set branch. -/
theorem TypedJournalUndoRecords.select_saved_values_in {F : Type} {widths : BitVec 64 → BitVec 64}
    {journal : BitVec 64} {count index : Nat} {state : PanSemStateFiniteExact 64 F}
    (valid : TypedJournalUndoRecords widths journal count state)
    (watched targets : Set (BitVec 64)) (saved : JournalSavedValuesIn journal count watched targets state)
    (inside : index < count) :
    ∃ table key present value : BitVec 64,
      (widths table = 20 ∨ widths table = 32 ∨ widths table = 52) ∧
      state.memory (journal + BitVec.ofNat 64 index * 32) = .word table ∧
      state.memory (journal + BitVec.ofNat 64 index * 32 + 8) = .word key ∧
      state.memory (journal + BitVec.ofNat 64 index * 32 + 16) = .word present ∧
      state.memory (journal + BitVec.ofNat 64 index * 32 + 24) = .word value ∧
      key.toNat % 8 = 0 ∧
      (∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset)) ∧
      (∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) ∧
      (table ∈ watched → present ≠ 0 → value ∈ targets) := by
  obtain ⟨table,key,present,value,supported,t,k,p,v,aligned,words,bytes⟩ := valid.select inside
  exact ⟨table,key,present,value,supported,t,k,p,v,aligned,words,bytes,saved index inside table present value t p v⟩

#print axioms JournalSavedValuesIn.empty
#print axioms JournalSavedValuesIn.shrink
#print axioms JournalSavedValuesIn.after_frame
#print axioms JournalSavedValuesIn.append
#print axioms TypedJournalUndoRecords.select_saved_values_in
end InitECandidate.Runtime
