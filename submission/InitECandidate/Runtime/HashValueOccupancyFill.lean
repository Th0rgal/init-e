import InitECandidate.Runtime.HashValueEntriesWord
import InitECandidate.Runtime.SourceByteReadback
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Marking occupancy and then writing a value preserves old slots and
establishes the marked slot's word shape. This is a memory lemma; the original
insertion evaluator writes its value before marking occupancy. -/
theorem HashValueEntriesWord.fill_and_write {F : Type}
    (state : PanSemStateFiniteExact 64 F) (used values capacity inserted cell value : BitVec 64)
    (entries : HashValueEntriesWord used values capacity state)
    (cellMemory : state.memory (panByteAlignHOL (used + inserted)) = .word cell)
    (valueOccupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ values + inserted * 8)
    (valuesSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ inserted →
      values + slot * 8 ≠ panByteAlignHOL (used + inserted) ∧
      values + slot * 8 ≠ values + inserted * 8) :
    HashValueEntriesWord used values capacity
      (sourceWriteWord (sourceWriteByte state (used + inserted) 1 cell) (values + inserted * 8) value) := by
  apply entries.write_slot state _ used values capacity inserted value
  · simp only [sourceWriteWord,ite_true]
  · intro slot inside different
    have separate : panByteAlignHOL (used + slot) ≠ values + inserted * 8#64 := valueOccupancy slot inside
    have byteRead := sourceWriteByte_load_other state (used + inserted) 1 cell (used + slot)
      (by simpa using different) cellMemory
    change hashOccupancyRead (sourceWriteWord (sourceWriteByte state (used + inserted) 1 cell)
      (values + inserted * 8) value) used slot = hashOccupancyRead state used slot
    have unchanged : hashOccupancyRead (sourceWriteWord (sourceWriteByte state (used + inserted) 1 cell)
        (values + inserted * 8) value) used slot =
        hashOccupancyRead (sourceWriteByte state (used + inserted) 1 cell) used slot := by
      simp [hashOccupancyRead,panMemLoadByteHOL,sourceWriteWord,separate]
      rfl
    exact unchanged.trans byteRead
  · intro slot inside different
    have separate := valuesSeparate slot inside different
    change (if values + slot * 8 = values + inserted * 8 then .word value
      else if values + slot * 8 = panByteAlignHOL (used + inserted) then _
      else state.memory (values + slot * 8)) = state.memory (values + slot * 8)
    rw [if_neg separate.2,if_neg separate.1]

#print axioms HashValueEntriesWord.fill_and_write
end InitECandidate.Runtime
