import InitECandidate.Runtime.HashReverseEntriesMoveStores
import InitECandidate.Runtime.HashDeleteOccupancyGeometryWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

theorem HashTableArraysInvariant.delete_reverse_separate_width {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count hole position : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (holeInside : hole.toNat < capacity.toNat) (positionInside : position.toNat < capacity.toNat) :
    ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ hole →
      orderPos + slot * 8 ≠ order + position * 8 ∧
      orderPos + slot * 8 ≠ orderPos + hole * 8 := by
  have orderBefore := invariant.orderBefore
  have bounded := invariant.endBound
  have reverseAddress : ∀ index : BitVec 64, index.toNat < capacity.toNat →
      (orderPos + index * 8).toNat = orderPos.toNat + index.toNat * 8 := by
    intro index inside
    exact (hashFind_slot_address orderPos index 8 capacity inside
      (by change orderPos.toNat + capacity.toNat * 8 ≤ 33806089496; exact bounded)
      invariant.orderPosAligned (by decide)).1
  have orderAddress := (hashFind_slot_address order position 8 capacity positionInside
    (by change order.toNat + capacity.toNat * 8 ≤ 33806089496; omega)
    invariant.orderAligned (by decide)).1
  change (order + position * 8).toNat = order.toNat + position.toNat * 8 at orderAddress
  have positionProduct := Nat.mul_lt_mul_of_pos_right positionInside (by decide : 0 < 8)
  intro slot inside different
  constructor
  · intro same
    have natural := congrArg BitVec.toNat same
    rw [reverseAddress slot inside,orderAddress] at natural
    omega
  · intro same
    have natural := congrArg BitVec.toNat same
    rw [reverseAddress slot inside,reverseAddress hole holeInside] at natural
    apply different
    apply BitVec.eq_of_toNat_eq
    omega

/-- Table geometry discharges all aliasing conditions for the actual movement
order stores, retaining the reverse invariant on occupied slots. -/
theorem HashReverseEntriesBound.move_stores_layout_width {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count hole position : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (entries : HashReverseEntriesBound used orderPos capacity count state)
    (holeInside : hole.toNat < capacity.toNat) (positionBound : position.toNat < count.toNat) :
    HashReverseEntriesBound used orderPos capacity count
      (sourceWriteWord (sourceWriteWord state (order + position * 8) hole) (orderPos + hole * 8) position) := by
  have positionInside : position.toNat < capacity.toNat := Nat.lt_trans positionBound invariant.room
  have occupancy := invariant.delete_occupancy_separate_width state keyLength table keys stride capacity used values order orderPos count
    hole position bits holeInside positionInside
  exact entries.move_stores state used order orderPos capacity count hole position positionBound
    (fun slot inside => (occupancy.2 slot inside).2)
    (invariant.delete_reverse_separate_width state keyLength table keys stride capacity used values order orderPos count hole position bits
      holeInside positionInside)

#print axioms HashTableArraysInvariant.delete_reverse_separate_width
#print axioms HashReverseEntriesBound.move_stores_layout_width
end InitECandidate.Runtime
