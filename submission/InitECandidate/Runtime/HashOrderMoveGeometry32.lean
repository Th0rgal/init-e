import InitECandidate.Runtime.HashOrderEntriesMove
import InitECandidate.Runtime.HashTableArraysRead32
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Array ordering and no-wrap word addresses discharge the forward order
movement-store obligations, including distinct live indices. -/
theorem HashOrderEntriesBound.move_stores_layout32 {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count hole position : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (entries : HashOrderEntriesBound order capacity count state)
    (holeInside : hole.toNat < capacity.toNat) (positionBound : position.toNat < count.toNat) :
    HashOrderEntriesBound order capacity count
      (sourceWriteWord (sourceWriteWord state (order + position * 8) hole) (orderPos + hole * 8) position) := by
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  have room := invariant.room
  have address : ∀ index : BitVec 64, index.toNat < capacity.toNat →
      (order + index * 8).toNat = order.toNat + index.toNat * 8 := by
    intro index inside
    exact (hashFind_slot_address order index 8 capacity inside
      (by change order.toNat + capacity.toNat * 8 ≤ 33806089496; omega)
      invariant.orderAligned (by decide)).1
  have reverseAddress := (hashFind_slot_address orderPos hole 8 capacity holeInside
    (by change orderPos.toNat + capacity.toNat * 8 ≤ 33806089496; exact bounded)
    invariant.orderPosAligned (by decide)).1
  change (orderPos + hole * 8).toNat = orderPos.toNat + hole.toNat * 8 at reverseAddress
  have separation : ∀ index : BitVec 64, index.toNat < count.toNat →
      order + index * 8 ≠ orderPos + hole * 8 := by
    intro index inside same
    have natural := congrArg BitVec.toNat same
    rw [address index (by omega),reverseAddress] at natural
    have product := Nat.mul_lt_mul_of_pos_right (show index.toNat < capacity.toNat by omega) (by decide : 0 < 8)
    omega
  apply entries.move_stores state order orderPos capacity count position hole holeInside separation
    (separation position positionBound)
  intro index inside different same
  have natural := congrArg BitVec.toNat same
  rw [address index (by omega),address position (by omega)] at natural
  apply different
  apply BitVec.eq_of_toNat_eq
  omega

#print axioms HashOrderEntriesBound.move_stores_layout32
end InitECandidate.Runtime
