import InitECandidate.Runtime.HashTableArraysHeaderFrame
import InitECandidate.Runtime.HashDeleteOccupancyGeometryWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

theorem HashTableArraysInvariant.after_word_width {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count destination value : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (header : ∀ offset ∈ ([0,8,16,24,32,40,48,56,64] : List Nat), table + BitVec.ofNat 64 offset ≠ destination)
    (occupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → panByteAlignHOL (used + slot) ≠ destination) :
    HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits (sourceWriteWord state destination value) := by
  apply invariant.framed state (sourceWriteWord state destination value) keyLength table keys stride capacity used values order orderPos count bits ?_ ?_ rfl rfl
  · intro offset member
    change (if table + BitVec.ofNat 64 offset = destination then HolWordLab.word value else _) = _
    rw [if_neg (header offset member)]
  · intro slot inside
    simp [hashOccupancyRead,panMemLoadByteHOL,sourceWriteWord,occupancy slot inside]
    rfl

/-- The actual value/order/reverse movement stores retain every table header and occupancy count. -/
theorem HashTableArraysInvariant.move_stores_width {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count hole position value : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (holeInside : hole.toNat < capacity.toNat) (positionBound : position.toNat < count.toNat) :
    HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits
      (sourceWriteWord (sourceWriteWord (sourceWriteWord state (values + hole * 8) value)
        (order + position * 8) hole) (orderPos + hole * 8) position) := by
  have hv := invariant.headerValues
  have vu := invariant.valuesBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  have positionInside := Nat.lt_trans positionBound invariant.room
  have va := (hashFind_slot_address values hole 8 capacity holeInside
    (by change values.toNat + capacity.toNat * 8 ≤ 33806089496; omega) invariant.valuesAligned (by decide)).1
  have oa := (hashFind_slot_address order position 8 capacity positionInside
    (by change order.toNat + capacity.toNat * 8 ≤ 33806089496; omega) invariant.orderAligned (by decide)).1
  have ra := (hashFind_slot_address orderPos hole 8 capacity holeInside
    (by change orderPos.toNat + capacity.toNat * 8 ≤ 33806089496; exact bounded) invariant.orderPosAligned (by decide)).1
  change (values + hole * 8).toNat = values.toNat + hole.toNat * 8 at va
  change (order + position * 8).toNat = order.toNat + position.toNat * 8 at oa
  change (orderPos + hole * 8).toNat = orderPos.toNat + hole.toNat * 8 at ra
  have headers : ∀ offset ∈ ([0,8,16,24,32,40,48,56,64] : List Nat),
      table + BitVec.ofNat 64 offset ≠ values + hole * 8 ∧
      table + BitVec.ofNat 64 offset ≠ order + position * 8 ∧
      table + BitVec.ofNat 64 offset ≠ orderPos + hole * 8 := by
    intro offset member
    have small : offset ≤ 64 := by simp at member; omega
    have natural : (BitVec.ofNat 64 offset).toNat = offset := by
      change offset % 2 ^ 64 = offset
      exact Nat.mod_eq_of_lt (by omega)
    have ha : (table + BitVec.ofNat 64 offset).toNat = table.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    refine ⟨?_,?_,?_⟩ <;> intro same <;> have equality := congrArg BitVec.toNat same
    · rw [ha,va] at equality; omega
    · rw [ha,oa] at equality; omega
    · rw [ha,ra] at equality; omega
  have occupancy := (invariant.delete_occupancy_separate_width state keyLength table keys stride capacity used values order orderPos count hole position bits holeInside positionInside).2
  have first := invariant.after_word_width state keyLength table keys stride capacity used values order orderPos count (values + hole * 8) value bits
    (fun offset member => (headers offset member).1) (fun slot inside => (occupancy slot inside).1)
  have second := first.after_word_width _ keyLength table keys stride capacity used values order orderPos count (order + position * 8) hole bits
    (fun offset member => (headers offset member).2.1) (fun slot inside => (occupancy slot inside).2.1)
  exact second.after_word_width _ keyLength table keys stride capacity used values order orderPos count (orderPos + hole * 8) position bits
    (fun offset member => (headers offset member).2.2) (fun slot inside => (occupancy slot inside).2.2)

#print axioms HashTableArraysInvariant.after_word_width
#print axioms HashTableArraysInvariant.move_stores_width
end InitECandidate.Runtime
