import InitECandidate.Runtime.HashValueOccupancyFill
import InitECandidate.Runtime.HashValueWriteGeometry32
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The occupancy-then-value memory sequence preserves readable values
using table geometry, including shared occupancy words and distinct slots. -/
theorem HashValueEntriesWord.fill_and_write_layout32 {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count inserted cell value : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (entries : HashValueEntriesWord used values capacity state)
    (inside : inserted.toNat < capacity.toNat)
    (cellMemory : state.memory (panByteAlignHOL (used + inserted)) = .word cell) :
    HashValueEntriesWord used values capacity
      (sourceWriteWord (sourceWriteByte state (used + inserted) 1 cell) (values + inserted * 8) value) := by
  have vu := invariant.valuesBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have limit := invariant.endBound
  have occupancy := hashSet_value_separate values used capacity inserted inside invariant.valuesAligned
    invariant.usedAligned vu (by omega)
  have address : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      (values + slot * 8).toNat = values.toNat + slot.toNat * 8 := by
    intro slot bound
    exact (hashFind_slot_address values slot 8 capacity bound
      (by change values.toNat + capacity.toNat * 8 ≤ 33806089496; omega)
      invariant.valuesAligned (by decide)).1
  apply entries.fill_and_write state used values capacity inserted cell value cellMemory occupancy
  intro slot bound different
  constructor
  · have separate := hashSet_value_separate values used capacity slot bound invariant.valuesAligned
      invariant.usedAligned vu (by omega)
    exact Ne.symm (separate inserted inside)
  · intro same
    have natural := congrArg BitVec.toNat same
    rw [address slot bound,address inserted inside] at natural
    apply different
    apply BitVec.eq_of_toNat_eq
    omega

#print axioms HashValueEntriesWord.fill_and_write_layout32
end InitECandidate.Runtime
