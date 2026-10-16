import InitECandidate.Runtime.HashValueWordStores
import InitECandidate.Runtime.HashTableArraysRead32
import InitECandidate.Runtime.HashSetExisting
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Bounded value-array addresses distinguish slots, while the occupancy
allocation lies after every value cell. -/
theorem HashValueEntriesWord.write_value_layout32 {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count changed value : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (entries : HashValueEntriesWord used values capacity state)
    (inside : changed.toNat < capacity.toNat) :
    HashValueEntriesWord used values capacity (sourceWriteWord state (values + changed * 8) value) := by
  have vu := invariant.valuesBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have limit := invariant.endBound
  have occupancy := hashSet_value_separate values used capacity changed inside invariant.valuesAligned
    invariant.usedAligned vu (by omega)
  have address : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      (values + slot * 8).toNat = values.toNat + slot.toNat * 8 := by
    intro slot bound
    exact (hashFind_slot_address values slot 8 capacity bound
      (by change values.toNat + capacity.toNat * 8 ≤ 33806089496; omega)
      invariant.valuesAligned (by decide)).1
  apply entries.write_value state used values capacity changed value occupancy
  intro slot bound different same
  have natural := congrArg BitVec.toNat same
  rw [address slot bound,address changed inside] at natural
  apply different
  apply BitVec.eq_of_toNat_eq
  omega

#print axioms HashValueEntriesWord.write_value_layout32
end InitECandidate.Runtime
