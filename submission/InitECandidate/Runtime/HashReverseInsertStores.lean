import InitECandidate.Runtime.HashReverseEntriesUpdate
import InitECandidate.Runtime.SourceByteReadback
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Marking occupancy and performing insertion bookkeeping initializes the
new reverse entry and preserves bounded reverse positions for old slots. -/
theorem HashReverseEntriesBound.insert_stores {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (used order orderPos capacity items inserted table cell : BitVec 64)
    (entries : HashReverseEntriesBound used orderPos capacity items state)
    (noWrap : items.toNat + 1 < 2 ^ 64)
    (cellMemory : state.memory (panByteAlignHOL (used + inserted)) = HolWordLab.word cell)
    (newSeparate : orderPos + inserted * 8 ≠ table + 24)
    (occupancySeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ order + items * 8 ∧
      panByteAlignHOL (used + slot) ≠ orderPos + inserted * 8 ∧
      panByteAlignHOL (used + slot) ≠ table + 24)
    (reverseSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ inserted →
      orderPos + slot * 8 ≠ panByteAlignHOL (used + inserted) ∧
      orderPos + slot * 8 ≠ order + items * 8 ∧
      orderPos + slot * 8 ≠ orderPos + inserted * 8 ∧ orderPos + slot * 8 ≠ table + 24) :
    HashReverseEntriesBound used orderPos capacity (items + 1)
      (sourceWriteWord (sourceWriteWord (sourceWriteWord
        (sourceWriteByte state (used + inserted) 1 cell) (order + items * 8) inserted)
        (orderPos + inserted * 8) items) (table + 24) (items + 1)) := by
  apply entries.insert state _ used orderPos capacity items inserted noWrap
  · change (if orderPos + inserted * 8 = table + 24 then HolWordLab.word (items + 1)
      else if orderPos + inserted * 8 = orderPos + inserted * 8 then HolWordLab.word items else _) = HolWordLab.word items
    rw [if_neg newSeparate,if_pos rfl]
  · intro slot inside different
    have separate := occupancySeparate slot inside
    have so : panByteAlignHOL (used + slot) ≠ order + items * 8#64 := separate.1
    have sr : panByteAlignHOL (used + slot) ≠ orderPos + inserted * 8#64 := separate.2.1
    have st : panByteAlignHOL (used + slot) ≠ table + 24#64 := separate.2.2
    have byteRead := sourceWriteByte_load_other state (used + inserted) 1 cell (used + slot)
      (by simpa using different) cellMemory
    change hashOccupancyRead (sourceWriteByte state (used + inserted) 1 cell) used slot =
      hashOccupancyRead state used slot at byteRead
    have stable (s : PanSemStateFiniteExact 64 F) (destination word : BitVec 64)
        (differentCell : panByteAlignHOL (used + slot) ≠ destination) :
        hashOccupancyRead (sourceWriteWord s destination word) used slot = hashOccupancyRead s used slot := by
      simp [hashOccupancyRead,panMemLoadByteHOL,sourceWriteWord,differentCell]
      rfl
    exact (stable _ (table + 24) (items + 1) separate.2.2).trans
      ((stable _ (orderPos + inserted * 8) items separate.2.1).trans
        ((stable _ (order + items * 8) inserted separate.1).trans byteRead))
  · intro slot inside different
    have separate := reverseSeparate slot inside different
    change (if orderPos + slot * 8 = table + 24 then HolWordLab.word (items + 1)
      else if orderPos + slot * 8 = orderPos + inserted * 8 then HolWordLab.word items
      else if orderPos + slot * 8 = order + items * 8 then HolWordLab.word inserted
      else if orderPos + slot * 8 = panByteAlignHOL (used + inserted) then _
      else state.memory (orderPos + slot * 8)) = state.memory (orderPos + slot * 8)
    rw [if_neg separate.2.2.2,if_neg separate.2.2.1,if_neg separate.2.1,if_neg separate.1]

#print axioms HashReverseEntriesBound.insert_stores
end InitECandidate.Runtime
