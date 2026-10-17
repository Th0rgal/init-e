import InitECandidate.Runtime.HashTableValuesInMutation
import InitECandidate.Runtime.SourceByteReadback
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Bookkeeping word stores preserve pointer membership when the three
relevant header fields, occupancy bytes, and value cells are separate. -/
theorem HashTableValuesIn.after_word_separate {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table capacity used values destination word : BitVec 64) (targets : Set (BitVec 64))
    (entries : HashTableValuesIn table targets state)
    (capField : state.memory (table + 16) = .word capacity)
    (usedField : state.memory (table + 48) = .word used) (valuesField : state.memory (table + 40) = .word values)
    (headerSeparate : ∀ offset ∈ ([16,40,48] : List Nat), table + BitVec.ofNat 64 offset ≠ destination)
    (occupancySeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → panByteAlignHOL (used + slot) ≠ destination)
    (valuesSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → values + slot * 8 ≠ destination) :
    HashTableValuesIn table targets (sourceWriteWord state destination word) := by
  have headerFrame (offset : Nat) (member : offset ∈ ([16,40,48] : List Nat)) :
      (sourceWriteWord state destination word).memory (table + BitVec.ofNat 64 offset) = state.memory (table + BitVec.ofNat 64 offset) := by
    change (if table + BitVec.ofNat 64 offset = destination then HolWordLab.word word else _) = _
    rw [if_neg (headerSeparate offset member)]
  apply HashTableValuesIn.of_entries _ table capacity used values targets
    ((headerFrame 16 (by simp)).trans capField) ((headerFrame 48 (by simp)).trans usedField) ((headerFrame 40 (by simp)).trans valuesField)
  intro slot inside occupied value cell
  have reads : hashOccupancyRead (sourceWriteWord state destination word) used slot = hashOccupancyRead state used slot := by
    simp [hashOccupancyRead,panMemLoadByteHOL,sourceWriteWord,occupancySeparate slot inside]
    rfl
  have memory : (sourceWriteWord state destination word).memory (values + slot * 8) = state.memory (values + slot * 8) := by
    change (if values + slot * 8 = destination then HolWordLab.word word else _) = _
    rw [if_neg (valuesSeparate slot inside)]
  exact entries capacity used values capField usedField valuesField slot inside
    (by rw [← reads]; exact occupied) value (memory.symm.trans cell)

/-- Marking a new occupancy byte is safe once its value cell contains a
registered pointer; neighboring bytes retain their original meanings. -/
theorem HashTableValuesIn.mark_occupied {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table capacity used values inserted cell value : BitVec 64) (targets : Set (BitVec 64))
    (entries : HashTableValuesIn table targets state) (member : value ∈ targets) (inside : inserted.toNat < capacity.toNat)
    (capField : state.memory (table + 16) = .word capacity)
    (usedField : state.memory (table + 48) = .word used) (valuesField : state.memory (table + 40) = .word values)
    (cellMemory : state.memory (panByteAlignHOL (used + inserted)) = .word cell)
    (written : state.memory (values + inserted * 8) = .word value)
    (headerSeparate : ∀ offset ∈ ([16,40,48] : List Nat), table + BitVec.ofNat 64 offset ≠ panByteAlignHOL (used + inserted))
    (valuesSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → values + slot * 8 ≠ panByteAlignHOL (used + inserted)) :
    HashTableValuesIn table targets (sourceWriteByte state (used + inserted) 1 cell) := by
  have headerFrame (offset : Nat) (atHeader : offset ∈ ([16,40,48] : List Nat)) :=
    sourceWriteByte_memory_other state (used + inserted) 1 cell (table + BitVec.ofNat 64 offset) (headerSeparate offset atHeader)
  apply entries.write_slot state _ table capacity used values inserted value targets member capField usedField valuesField
    ((headerFrame 16 (by simp)).trans capField) ((headerFrame 48 (by simp)).trans usedField) ((headerFrame 40 (by simp)).trans valuesField)
  · exact (sourceWriteByte_memory_other state (used + inserted) 1 cell _ (valuesSeparate inserted inside)).trans written
  · intro slot inside different
    exact sourceWriteByte_load_other state (used + inserted) 1 cell (used + slot) (by simpa using different) cellMemory
  · intro slot inside _
    exact sourceWriteByte_memory_other state (used + inserted) 1 cell _ (valuesSeparate slot inside)

#print axioms HashTableValuesIn.after_word_separate
#print axioms HashTableValuesIn.mark_occupied
end InitECandidate.Runtime
