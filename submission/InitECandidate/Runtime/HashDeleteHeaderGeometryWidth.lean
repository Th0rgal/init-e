import InitECandidate.Runtime.HashDeleteFinalSeparationWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- All non-count table headers precede the final order/reverse stores and
are distinct from the count header. -/
theorem HashTableArraysInvariant.delete_final_header_separation_width {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos items deletedPosition lastSlot : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
    (deletedInside : deletedPosition.toNat < items.toNat) (lastInside : lastSlot.toNat < capacity.toNat) :
    ∀ offset : Nat, offset ≤ 64 → offset ≠ 24 →
      table + BitVec.ofNat 64 offset ≠ order + deletedPosition * 8 ∧
      table + BitVec.ofNat 64 offset ≠ orderPos + lastSlot * 8 ∧
      table + BitVec.ofNat 64 offset ≠ table + 24 := by
  have hk := invariant.headerKeys
  have ku := invariant.keysBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  have room := invariant.room
  have oa := (hashFind_slot_address order deletedPosition 8 capacity (Nat.lt_trans deletedInside room)
    (by change order.toNat + capacity.toNat * 8 ≤ 33806089496; omega) invariant.orderAligned (by decide)).1
  have ra := (hashFind_slot_address orderPos lastSlot 8 capacity lastInside
    (by change orderPos.toNat + capacity.toNat * 8 ≤ 33806089496; exact bounded) invariant.orderPosAligned (by decide)).1
  change (order + deletedPosition * 8).toNat = order.toNat + deletedPosition.toNat * 8 at oa
  change (orderPos + lastSlot * 8).toNat = orderPos.toNat + lastSlot.toNat * 8 at ra
  have ca : (table + (24 : BitVec 64)).toNat = table.toNat + 24 := by
    rw [BitVec.toNat_add_of_lt (by change table.toNat + 24 < 2 ^ 64; omega)]
    rfl
  intro offset small notCount
  have natural : (BitVec.ofNat 64 offset).toNat = offset := by
    change offset % 2 ^ 64 = offset
    exact Nat.mod_eq_of_lt (by omega)
  have ha : (table + BitVec.ofNat 64 offset).toNat = table.toNat + offset := by
    rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
  refine ⟨?_,?_,?_⟩ <;> intro same <;> have equal := congrArg BitVec.toNat same
  · rw [ha,oa] at equal; omega
  · rw [ha,ra] at equal; omega
  · rw [ha,ca] at equal; omega

/-- The occupancy clear lies beyond every table header cell. -/
theorem HashTableArraysInvariant.delete_clear_header_separation_width {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos items hole : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
    (inside : hole.toNat < capacity.toNat) :
    ∀ offset : Nat, offset ≤ 64 → table + BitVec.ofNat 64 offset ≠ panByteAlignHOL (used + hole) := by
  have hk := invariant.headerKeys
  have ku := invariant.keysBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  intro offset small
  have natural : (BitVec.ofNat 64 offset).toNat = offset := by
    change offset % 2 ^ 64 = offset
    exact Nat.mod_eq_of_lt (by omega)
  have address : (table + BitVec.ofNat 64 offset).toNat = table.toNat + offset := by
    rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
  exact Ne.symm (hashOccupancy_separate_allocation used capacity (table + BitVec.ofNat 64 offset)
    invariant.usedAligned (by omega) (Or.inl (by rw [address]; omega)) hole inside)

#print axioms HashTableArraysInvariant.delete_clear_header_separation_width
#print axioms HashTableArraysInvariant.delete_final_header_separation_width
end InitECandidate.Runtime
