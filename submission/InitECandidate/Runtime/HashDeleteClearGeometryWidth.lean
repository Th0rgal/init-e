import InitECandidate.Runtime.HashDeleteFinalSeparationWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Clearing occupancy cannot overwrite any live order cell or reverse cell. -/
theorem HashTableArraysInvariant.delete_clear_order_separation_width {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos items hole : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
    (holeInside : hole.toNat < capacity.toNat) :
    (∀ slot : BitVec 64, slot.toNat < capacity.toNat → orderPos + slot * 8 ≠ panByteAlignHOL (used + hole)) ∧
    (∀ position : BitVec 64, position.toNat < items.toNat → order + position * 8 ≠ panByteAlignHOL (used + hole)) ∧
    table + 24 ≠ panByteAlignHOL (used + hole) := by
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  have room := invariant.room
  have reverseAddress : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      (orderPos + slot * 8).toNat = orderPos.toNat + slot.toNat * 8 := by
    intro slot inside
    exact (hashFind_slot_address orderPos slot 8 capacity inside
      (by change orderPos.toNat + capacity.toNat * 8 ≤ 33806089496; exact bounded) invariant.orderPosAligned (by decide)).1
  have orderAddress : ∀ position : BitVec 64, position.toNat < capacity.toNat →
      (order + position * 8).toNat = order.toNat + position.toNat * 8 := by
    intro position inside
    exact (hashFind_slot_address order position 8 capacity inside
      (by change order.toNat + capacity.toNat * 8 ≤ 33806089496; omega) invariant.orderAligned (by decide)).1
  refine ⟨?_,?_,?_⟩
  · intro slot inside
    exact Ne.symm (hashOccupancy_separate_allocation used capacity (orderPos + slot * 8)
      invariant.usedAligned (by omega) (Or.inr (by rw [reverseAddress slot inside]; omega)) hole holeInside)
  · intro position inside
    exact Ne.symm (hashOccupancy_separate_allocation used capacity (order + position * 8)
      invariant.usedAligned (by omega) (Or.inr (by rw [orderAddress position (by omega)]; omega)) hole holeInside)
  · have facts := invariant.insertion_memory state keyLength table keys stride capacity used values order orderPos items bits
    exact Ne.symm ((facts.separate hole holeInside hole holeInside).2.2)

#print axioms HashTableArraysInvariant.delete_clear_order_separation_width
end InitECandidate.Runtime
