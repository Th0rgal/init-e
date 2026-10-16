import InitECandidate.Runtime.HashValueWordStores
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Insertion bookkeeping cannot change readable value words when its three
actual destination cells are outside the occupancy and value arrays. -/
theorem HashValueEntriesWord.insert_bookkeeping {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (used values capacity table order orderPos count inserted : BitVec 64)
    (entries : HashValueEntriesWord used values capacity state)
    (occupancySeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ order + count * 8 ∧
      panByteAlignHOL (used + slot) ≠ orderPos + inserted * 8 ∧
      panByteAlignHOL (used + slot) ≠ table + 24)
    (valuesSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      values + slot * 8 ≠ order + count * 8 ∧
      values + slot * 8 ≠ orderPos + inserted * 8 ∧
      values + slot * 8 ≠ table + 24) :
    HashValueEntriesWord used values capacity
      (sourceWriteWord (sourceWriteWord (sourceWriteWord state
        (order + count * 8) inserted) (orderPos + inserted * 8) count) (table + 24) (count + 1)) := by
  have ordered := entries.after_word state used values capacity (order + count * 8) inserted
    (fun slot inside => (occupancySeparate slot inside).1)
    (fun slot inside => (valuesSeparate slot inside).1)
  have reversed := ordered.after_word _ used values capacity (orderPos + inserted * 8) count
    (fun slot inside => (occupancySeparate slot inside).2.1)
    (fun slot inside => (valuesSeparate slot inside).2.1)
  exact reversed.after_word _ used values capacity (table + 24) (count + 1)
    (fun slot inside => (occupancySeparate slot inside).2.2)
    (fun slot inside => (valuesSeparate slot inside).2.2)

#print axioms HashValueEntriesWord.insert_bookkeeping
end InitECandidate.Runtime
