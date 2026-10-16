import InitECandidate.Runtime.HashValueEntriesWord
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Zero occupied count means every in-range byte is actually readable zero;
the count definition treats failed reads as occupied. -/
theorem hashOccupiedCount_zero_reads (capacity : BitVec 64) (read : BitVec 64 → Option UInt8)
    (empty : hashOccupiedCount capacity read = 0) :
    ∀ slot : BitVec 64, slot.toNat < capacity.toNat → read slot = some 0 := by
  intro slot inside
  unfold hashOccupiedCount at empty
  have absent := List.countP_eq_zero.mp empty slot.toNat (List.mem_range.mpr inside)
  have word : BitVec.ofNat 64 slot.toNat = slot := by simp
  simpa [word] using absent

theorem hashEmpty_entry_invariants {F : Type} (state : PanSemStateFiniteExact 64 F)
    (used values orderPos capacity : BitVec 64)
    (empty : hashOccupiedCount capacity (hashOccupancyRead state used) = 0) :
    HashValueEntriesWord used values capacity state ∧ HashReverseEntriesBound used orderPos capacity 0 state := by
  have zeroed := hashOccupiedCount_zero_reads capacity (hashOccupancyRead state used) empty
  exact ⟨HashValueEntriesWord.empty state used values capacity zeroed,
    HashReverseEntriesBound.empty state used orderPos capacity zeroed⟩

#print axioms hashOccupiedCount_zero_reads
#print axioms hashEmpty_entry_invariants
end InitECandidate.Runtime
