import InitECandidate.Runtime.HashValueEntriesWord
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A value write preserves readable words at every occupied slot. -/
theorem HashValueEntriesWord.write_value {F : Type}
    (state : PanSemStateFiniteExact 64 F) (used values capacity changed value : BitVec 64)
    (entries : HashValueEntriesWord used values capacity state)
    (occupancySeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ values + changed * 8)
    (distinct : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ changed →
      values + slot * 8 ≠ values + changed * 8) :
    HashValueEntriesWord used values capacity (sourceWriteWord state (values + changed * 8) value) := by
  apply entries.write_slot state _ used values capacity changed value
  · simp only [sourceWriteWord,ite_true]
  · intro slot inside different
    have separate : panByteAlignHOL (used + slot) ≠ values + changed * 8#64 := occupancySeparate slot inside
    simp [hashOccupancyRead,panMemLoadByteHOL,sourceWriteWord,separate]
    rfl
  · intro slot inside different
    change (if values + slot * 8 = values + changed * 8 then .word value
      else state.memory (values + slot * 8)) = state.memory (values + slot * 8)
    rw [if_neg (distinct slot inside different)]

/-- Other bookkeeping writes retain occupied value words when separate from
both occupancy and value arrays. -/
theorem HashValueEntriesWord.after_word {F : Type}
    (state : PanSemStateFiniteExact 64 F) (used values capacity destination word : BitVec 64)
    (entries : HashValueEntriesWord used values capacity state)
    (occupancySeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ destination)
    (valueSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → values + slot * 8 ≠ destination) :
    HashValueEntriesWord used values capacity (sourceWriteWord state destination word) := by
  intro slot inside occupied
  have reads : hashOccupancyRead (sourceWriteWord state destination word) used slot =
      hashOccupancyRead state used slot := by
    simp [hashOccupancyRead,panMemLoadByteHOL,sourceWriteWord,occupancySeparate slot inside]
    rfl
  obtain ⟨value,cell⟩ := entries slot inside (by rw [← reads]; exact occupied)
  refine ⟨value,?_⟩
  change (if values + slot * 8 = destination then .word word else state.memory (values + slot * 8)) = .word value
  rw [if_neg (valueSeparate slot inside)]
  exact cell

#print axioms HashValueEntriesWord.write_value
#print axioms HashValueEntriesWord.after_word
end InitECandidate.Runtime
