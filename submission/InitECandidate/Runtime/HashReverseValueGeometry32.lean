import InitECandidate.Runtime.HashReverseMoveGeometry32
import InitECandidate.Runtime.HashReverseWordFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

theorem HashTableArraysInvariant32.value_reverse_separate {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count hole : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (holeInside : hole.toNat < capacity.toNat) :
    ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      orderPos + slot * 8 ≠ values + hole * 8 := by
  have vu := invariant.valuesBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  have valueAddress := (hashFind_slot_address values hole 8 capacity holeInside
    (by change values.toNat + capacity.toNat * 8 ≤ 33806089496; omega)
    invariant.valuesAligned (by decide)).1
  change (values + hole * 8).toNat = values.toNat + hole.toNat * 8 at valueAddress
  have product := Nat.mul_lt_mul_of_pos_right holeInside (by decide : 0 < 8)
  intro slot inside same
  have reverseAddress := (hashFind_slot_address orderPos slot 8 capacity inside
    (by change orderPos.toNat + capacity.toNat * 8 ≤ 33806089496; exact bounded)
    invariant.orderPosAligned (by decide)).1
  change (orderPos + slot * 8).toNat = orderPos.toNat + slot.toNat * 8 at reverseAddress
  have equal := congrArg BitVec.toNat same
  rw [reverseAddress,valueAddress] at equal
  omega

/-- Layout alone supplies the aliasing obligations for all three movement
word stores. The stored reverse position must belong to the live order prefix. -/
theorem HashReverseEntriesBound.value_move_stores_layout32 {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count hole position value : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (entries : HashReverseEntriesBound used orderPos capacity count state)
    (holeInside : hole.toNat < capacity.toNat) (positionBound : position.toNat < count.toNat) :
    HashReverseEntriesBound used orderPos capacity count
      (sourceWriteWord (sourceWriteWord (sourceWriteWord state (values + hole * 8) value)
        (order + position * 8) hole) (orderPos + hole * 8) position) := by
  have positionInside := Nat.lt_trans positionBound invariant.room
  have occupancy := invariant.delete_occupancy_separate state table keys stride capacity used values order orderPos count
    hole position bits holeInside positionInside
  exact entries.value_move_stores state used order orderPos capacity count values hole position value positionBound
    (fun slot inside => (occupancy.2 slot inside).1)
    (invariant.value_reverse_separate state table keys stride capacity used values order orderPos count hole bits holeInside)
    (fun slot inside => (occupancy.2 slot inside).2)
    (invariant.delete_reverse_separate state table keys stride capacity used values order orderPos count hole position bits
      holeInside positionInside)

#print axioms HashTableArraysInvariant32.value_reverse_separate
#print axioms HashReverseEntriesBound.value_move_stores_layout32
end InitECandidate.Runtime
