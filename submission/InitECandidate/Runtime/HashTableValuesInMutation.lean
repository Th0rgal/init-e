import InitECandidate.Runtime.HashTableValuesIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Known header fields let slot-level membership establish the table predicate. -/
theorem HashTableValuesIn.of_entries {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table capacity used values : BitVec 64) (targets : Set (BitVec 64))
    (capField : state.memory (table + 16) = .word capacity)
    (usedField : state.memory (table + 48) = .word used)
    (valuesField : state.memory (table + 40) = .word values)
    (slots : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → hashOccupancyRead state used slot ≠ some 0 →
      ∀ value : BitVec 64, state.memory (values + slot * 8) = .word value → value ∈ targets) :
    HashTableValuesIn table targets state := by
  intro otherCapacity otherUsed otherValues capCell usedCell valuesCell
  have capEq : otherCapacity = capacity := by simpa only [HolWordLab.word.injEq] using capCell.symm.trans capField
  have usedEq : otherUsed = used := by simpa only [HolWordLab.word.injEq] using usedCell.symm.trans usedField
  have valuesEq : otherValues = values := by simpa only [HolWordLab.word.injEq] using valuesCell.symm.trans valuesField
  subst otherCapacity; subst otherUsed; subst otherValues
  exact slots

/-- A registered value can replace one slot, or occupy a previously empty slot,
while all other occupancy bytes and value cells retain their meanings. -/
theorem HashTableValuesIn.write_slot {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (table capacity used values changed writtenValue : BitVec 64) (targets : Set (BitVec 64))
    (entries : HashTableValuesIn table targets state) (member : writtenValue ∈ targets)
    (capField : state.memory (table + 16) = .word capacity)
    (usedField : state.memory (table + 48) = .word used) (valuesField : state.memory (table + 40) = .word values)
    (capAfter : post.memory (table + 16) = .word capacity)
    (usedAfter : post.memory (table + 48) = .word used) (valuesAfter : post.memory (table + 40) = .word values)
    (written : post.memory (values + changed * 8) = .word writtenValue)
    (occupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ changed →
      hashOccupancyRead post used slot = hashOccupancyRead state used slot)
    (frame : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ changed →
      post.memory (values + slot * 8) = state.memory (values + slot * 8)) :
    HashTableValuesIn table targets post := by
  apply HashTableValuesIn.of_entries post table capacity used values targets capAfter usedAfter valuesAfter
  intro slot inside occupied value cell
  by_cases same : slot = changed
  · subst slot
    have equal : writtenValue = value := by simpa only [HolWordLab.word.injEq] using written.symm.trans cell
    simpa only [← equal] using member
  · exact entries capacity used values capField usedField valuesField slot inside
      (by rw [← occupancy slot inside same]; exact occupied) value ((frame slot inside same).symm.trans cell)

/-- Deletion cannot introduce an unregistered pointer: the erased slot becomes
empty and all surviving occupied value cells are framed. -/
theorem HashTableValuesIn.erase_slot {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (table capacity used values changed : BitVec 64) (targets : Set (BitVec 64))
    (entries : HashTableValuesIn table targets state)
    (capField : state.memory (table + 16) = .word capacity)
    (usedField : state.memory (table + 48) = .word used) (valuesField : state.memory (table + 40) = .word values)
    (capAfter : post.memory (table + 16) = .word capacity)
    (usedAfter : post.memory (table + 48) = .word used) (valuesAfter : post.memory (table + 40) = .word values)
    (erased : hashOccupancyRead post used changed = some 0)
    (occupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ changed →
      hashOccupancyRead post used slot = hashOccupancyRead state used slot)
    (frame : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ changed →
      post.memory (values + slot * 8) = state.memory (values + slot * 8)) :
    HashTableValuesIn table targets post := by
  apply HashTableValuesIn.of_entries post table capacity used values targets capAfter usedAfter valuesAfter
  intro slot inside occupied value cell
  by_cases same : slot = changed
  · subst slot; exact False.elim (occupied erased)
  · exact entries capacity used values capField usedField valuesField slot inside
      (by rw [← occupancy slot inside same]; exact occupied) value ((frame slot inside same).symm.trans cell)

#print axioms HashTableValuesIn.of_entries
#print axioms HashTableValuesIn.write_slot
#print axioms HashTableValuesIn.erase_slot
end InitECandidate.Runtime
