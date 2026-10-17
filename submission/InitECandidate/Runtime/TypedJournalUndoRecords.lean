import InitECandidate.Runtime.JournalUndoRecords
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The fixed table-width map ties each saved key's accessible extent to the
table referenced by its record. Relocation can change arrays but not this map. -/
def TypedJournalUndoRecords {F : Type} (widths : BitVec 64 → BitVec 64)
    (journal : BitVec 64) (count : Nat) (state : PanSemStateFiniteExact 64 F) : Prop :=
  JournalUndoRecords journal count state ∧
    ∀ index : Nat, index < count → ∀ table key : BitVec 64,
      state.memory (journal + BitVec.ofNat 64 index * 32) = .word table →
      state.memory (journal + BitVec.ofNat 64 index * 32 + 8) = .word key →
      (widths table = 20 ∨ widths table = 32 ∨ widths table = 52) ∧
      (∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset)) ∧
      (∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))

theorem TypedJournalUndoRecords.shrink {F : Type} {widths : BitVec 64 → BitVec 64}
    {journal : BitVec 64} {count remaining : Nat} {state : PanSemStateFiniteExact 64 F}
    (valid : TypedJournalUndoRecords widths journal count state) (bound : remaining ≤ count) :
    TypedJournalUndoRecords widths journal remaining state := by
  exact ⟨valid.1.shrink bound,fun index inside => valid.2 index (by omega)⟩

theorem TypedJournalUndoRecords.after_frame {F : Type} {widths : BitVec 64 → BitVec 64}
    {journal : BitVec 64} {count remaining : Nat} {before after : PanSemStateFiniteExact 64 F}
    (valid : TypedJournalUndoRecords widths journal count before) (bound : remaining ≤ count)
    (domain : after.memaddrs = before.memaddrs)
    (frame : ∀ index : Nat, index < remaining → ∀ offset ∈ ([0,8,16,24] : List Nat),
      after.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) =
        before.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset)) :
    TypedJournalUndoRecords widths journal remaining after := by
  refine ⟨valid.1.after_frame bound domain frame,?_⟩
  intro index inside table key tableCell keyCell
  have tableFrame := frame index inside 0 (by simp)
  have keyFrame := frame index inside 8 (by simp)
  have oldTable : before.memory (journal + BitVec.ofNat 64 index * 32) = .word table := by
    simpa using tableFrame.symm.trans (by simpa using tableCell)
  have oldKey : before.memory (journal + BitVec.ofNat 64 index * 32 + 8) = .word key := keyFrame.symm.trans keyCell
  obtain ⟨supported,words,bytes⟩ := valid.2 index (by omega) table key oldTable oldKey
  exact ⟨supported,by simpa only [domain] using words,by simpa only [domain] using bytes⟩

/-- Select a record with the exact key extent required by its referenced table. -/
theorem TypedJournalUndoRecords.select {F : Type} {widths : BitVec 64 → BitVec 64}
    {journal : BitVec 64} {count index : Nat} {state : PanSemStateFiniteExact 64 F}
    (valid : TypedJournalUndoRecords widths journal count state) (inside : index < count) :
    ∃ table key present value : BitVec 64,
      (widths table = 20 ∨ widths table = 32 ∨ widths table = 52) ∧
      state.memory (journal + BitVec.ofNat 64 index * 32) = .word table ∧
      state.memory (journal + BitVec.ofNat 64 index * 32 + 8) = .word key ∧
      state.memory (journal + BitVec.ofNat 64 index * 32 + 16) = .word present ∧
      state.memory (journal + BitVec.ofNat 64 index * 32 + 24) = .word value ∧
      key.toNat % 8 = 0 ∧
      (∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset)) ∧
      (∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) := by
  obtain ⟨table,key,present,value,_,_,t,k,p,v,_,aligned,_,_⟩ := valid.1 index inside
  obtain ⟨supported,words,bytes⟩ := valid.2 index inside table key t k
  exact ⟨table,key,present,value,supported,t,k,p,v,aligned,words,bytes⟩

#print axioms TypedJournalUndoRecords.shrink
#print axioms TypedJournalUndoRecords.after_frame
#print axioms TypedJournalUndoRecords.select
end InitECandidate.Runtime
