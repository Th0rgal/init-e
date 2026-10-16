import InitECandidate.Runtime.HashValueWordStores
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The movement's value copy and two bookkeeping stores retain word values
at occupied slots. Separation concerns actual occupancy and value cells. -/
theorem HashValueEntriesWord.move_stores {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (used values order orderPos capacity hole position value : BitVec 64)
    (entries : HashValueEntriesWord used values capacity state)
    (valueOccupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ values + hole * 8)
    (distinct : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ hole →
      values + slot * 8 ≠ values + hole * 8)
    (orderOccupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ order + position * 8)
    (orderValues : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      values + slot * 8 ≠ order + position * 8)
    (reverseOccupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ orderPos + hole * 8)
    (reverseValues : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      values + slot * 8 ≠ orderPos + hole * 8) :
    HashValueEntriesWord used values capacity
      (sourceWriteWord (sourceWriteWord (sourceWriteWord state (values + hole * 8) value)
        (order + position * 8) hole) (orderPos + hole * 8) position) := by
  have written := entries.write_value state used values capacity hole value valueOccupancy distinct
  have ordered := written.after_word _ used values capacity (order + position * 8) hole orderOccupancy orderValues
  exact ordered.after_word _ used values capacity (orderPos + hole * 8) position reverseOccupancy reverseValues

#print axioms HashValueEntriesWord.move_stores
end InitECandidate.Runtime
