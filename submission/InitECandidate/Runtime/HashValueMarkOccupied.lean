import InitECandidate.Runtime.HashValueEntriesWord
import InitECandidate.Runtime.SourceByteReadback
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Original insertion marks occupancy after its value write. The new slot
must already contain a word; other slots retain both occupancy and values. -/
theorem HashValueEntriesWord.mark_occupied {F : Type}
    (state : PanSemStateFiniteExact 64 F) (used values capacity inserted cell value : BitVec 64)
    (entries : HashValueEntriesWord used values capacity state)
    (cellMemory : state.memory (panByteAlignHOL (used + inserted)) = .word cell)
    (written : state.memory (values + inserted * 8) = .word value)
    (separate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      values + slot * 8 ≠ panByteAlignHOL (used + inserted)) :
    HashValueEntriesWord used values capacity (sourceWriteByte state (used + inserted) 1 cell) := by
  intro slot inside occupied
  have frame := sourceWriteByte_memory_other state (used + inserted) 1 cell (values + slot * 8)
    (separate slot inside)
  by_cases same : slot = inserted
  · subst slot
    exact ⟨value,frame.trans written⟩
  · have reads := sourceWriteByte_load_other state (used + inserted) 1 cell (used + slot)
      (by simpa using same) cellMemory
    change hashOccupancyRead (sourceWriteByte state (used + inserted) 1 cell) used slot =
      hashOccupancyRead state used slot at reads
    obtain ⟨previous,memory⟩ := entries slot inside (by rw [← reads]; exact occupied)
    exact ⟨previous,frame.trans memory⟩

#print axioms HashValueEntriesWord.mark_occupied
end InitECandidate.Runtime
