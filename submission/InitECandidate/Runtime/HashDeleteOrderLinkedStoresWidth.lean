import InitECandidate.Runtime.HashDeleteOrderLinkedStores
import InitECandidate.Runtime.HashDeleteMoveAllocatedWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Derive all move-store separation from the allocated table layout. -/
theorem HashDeleteOrderLinked.move_stores_layout_width {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos items hole scan deletedPosition position value : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
    (linked : HashDeleteOrderLinked used order orderPos capacity items hole deletedPosition state)
    (holeInside : hole.toNat < capacity.toNat) (scanInside : scan.toNat < capacity.toNat)
    (different : scan ≠ hole) (occupied : hashOccupancyRead state used scan ≠ some 0)
    (cell : state.memory (orderPos + scan * 8) = .word position) :
    HashDeleteOrderLinked used order orderPos capacity items scan deletedPosition
      (sourceWriteWord (sourceWriteWord (sourceWriteWord state (values + hole * 8) value)
        (order + position * 8) hole) (orderPos + hole * 8) position) := by
  obtain ⟨actual,actualBound,_,actualCell,_⟩ := linked scan scanInside different occupied
  have equal : actual = position := by
    have words := actualCell.symm.trans cell
    injection words
  have positionBound : position.toNat < items.toNat := by simpa [equal] using actualBound
  have occupancy := (invariant.delete_occupancy_separate_width state keyLength table keys stride capacity used values order orderPos items hole position bits
    holeInside (Nat.lt_trans positionBound invariant.room)).2
  have valueReverse := invariant.value_reverse_separate_width state keyLength table keys stride capacity used values order orderPos items hole bits holeInside
  have storeReverse := invariant.delete_reverse_separate_width state keyLength table keys stride capacity used values order orderPos items hole position bits
    holeInside (Nat.lt_trans positionBound invariant.room)
  have valueSeparate := (invariant.delete_order_frames_width state keyLength table keys stride capacity used values order orderPos items hole bits holeInside).2
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  have room := invariant.room
  have orderAddress : ∀ index : BitVec 64, index.toNat < capacity.toNat →
      (order + index * 8).toNat = order.toNat + index.toNat * 8 := by
    intro index inside
    exact (hashFind_slot_address order index 8 capacity inside
      (by change order.toNat + capacity.toNat * 8 ≤ 33806089496; omega) invariant.orderAligned (by decide)).1
  have reverseAddress := (hashFind_slot_address orderPos hole 8 capacity holeInside
    (by change orderPos.toNat + capacity.toNat * 8 ≤ 33806089496; exact bounded) invariant.orderPosAligned (by decide)).1
  change (orderPos + hole * 8).toNat = orderPos.toNat + hole.toNat * 8 at reverseAddress
  have orderSeparate : ∀ index : BitVec 64, index.toNat < items.toNat → order + index * 8 ≠ orderPos + hole * 8 := by
    intro index inside same
    have natural := congrArg BitVec.toNat same
    rw [orderAddress index (by omega),reverseAddress] at natural
    have product := Nat.mul_lt_mul_of_pos_right (show index.toNat < capacity.toNat by omega) (by decide : 0 < 8)
    omega
  have positionSeparate := orderSeparate position positionBound
  have distinct : ∀ index : BitVec 64, index.toNat < items.toNat → index ≠ position → order + index * 8 ≠ order + position * 8 := by
    intro index inside different same
    have natural := congrArg BitVec.toNat same
    rw [orderAddress index (by omega),orderAddress position (by omega)] at natural
    exact different (BitVec.eq_of_toNat_eq (by omega))
  exact linked.move_stores state used order orderPos capacity items hole scan deletedPosition position value values
    scanInside different occupied cell occupancy
    (fun slot inside notHole => ⟨valueReverse slot inside,(storeReverse slot inside notHole).1,(storeReverse slot inside notHole).2⟩)
    (fun index inside notPosition => ⟨valueSeparate index inside,distinct index inside notPosition,orderSeparate index inside⟩)
    positionSeparate

#print axioms HashDeleteOrderLinked.move_stores_layout_width
end InitECandidate.Runtime
