import InitECandidate.Runtime.StateRestoreIterationPreserves
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Every live undo record has four accessible word fields and a supported,
aligned key. Table readiness is tracked separately because tables may grow. -/
def JournalUndoRecords {F : Type} (journal : BitVec 64) (count : Nat)
    (state : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ index : Nat, index < count → ∃ table key present value keyLength : BitVec 64,
    (keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52) ∧
    state.memory (journal + BitVec.ofNat 64 index * 32) = .word table ∧
    state.memory (journal + BitVec.ofNat 64 index * 32 + 8) = .word key ∧
    state.memory (journal + BitVec.ofNat 64 index * 32 + 16) = .word present ∧
    state.memory (journal + BitVec.ofNat 64 index * 32 + 24) = .word value ∧
    (∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset)) ∧
    key.toNat % 8 = 0 ∧
    (∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset)) ∧
    (∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))

theorem JournalUndoRecords.shrink {F : Type} {journal : BitVec 64} {count remaining : Nat}
    {state : PanSemStateFiniteExact 64 F} (valid : JournalUndoRecords journal count state)
    (bound : remaining ≤ count) : JournalUndoRecords journal remaining state := by
  intro index inside
  exact valid index (by omega)

/-- Only the live record cells and address domain need framing; the table
arrays and heap frontier may change during restoration. -/
theorem JournalUndoRecords.after_frame {F : Type} {journal : BitVec 64} {count remaining : Nat}
    {before after : PanSemStateFiniteExact 64 F} (valid : JournalUndoRecords journal count before)
    (bound : remaining ≤ count) (domain : after.memaddrs = before.memaddrs)
    (frame : ∀ index : Nat, index < remaining → ∀ offset ∈ ([0,8,16,24] : List Nat),
      after.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) =
        before.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset)) :
    JournalUndoRecords journal remaining after := by
  intro index inside
  obtain ⟨table,key,present,value,keyLength,supported,t,k,p,v,fields,aligned,words,bytes⟩ := valid index (by omega)
  refine ⟨table,key,present,value,keyLength,supported,?_,?_,?_,?_,?_,aligned,?_,?_⟩
  · simpa using (frame index inside 0 (by simp)).trans (by simpa using t)
  · exact (frame index inside 8 (by simp)).trans k
  · exact (frame index inside 16 (by simp)).trans p
  · exact (frame index inside 24 (by simp)).trans v
  · simpa only [domain] using fields
  · simpa only [domain] using words
  · simpa only [domain] using bytes

/-- A true rollback guard selects the last live record without word underflow. -/
theorem JournalUndoRecords.last_index {F : Type} {journal count snapshot : BitVec 64}
    {state : PanSemStateFiniteExact 64 F} (valid : JournalUndoRecords journal count.toNat state)
    (active : snapshot.toNat < count.toNat) :
    (count - 1).toNat < count.toNat ∧ JournalUndoRecords journal (count - 1).toNat state := by
  have decrement := (stateRestore_rank_decreases count snapshot active).1
  have inside : (count - 1).toNat < count.toNat := by omega
  exact ⟨inside,valid.shrink (Nat.le_of_lt inside)⟩

#print axioms JournalUndoRecords.shrink
#print axioms JournalUndoRecords.after_frame
#print axioms JournalUndoRecords.last_index
end InitECandidate.Runtime
