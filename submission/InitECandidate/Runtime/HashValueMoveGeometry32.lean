import InitECandidate.Runtime.HashValueWriteGeometry32
import InitECandidate.Runtime.HashReverseValueGeometry32
import InitECandidate.Runtime.HashOrderCopyGeometry32
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Concrete movement stores retain word-valued occupied slots using only
the bounded table layout and in-range hole/live-position bounds. -/
theorem HashValueEntriesWord.move_stores_layout32 {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count hole position value : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (entries : HashValueEntriesWord used values capacity state)
    (holeInside : hole.toNat < capacity.toNat) (positionBound : position.toNat < count.toNat) :
    HashValueEntriesWord used values capacity
      (sourceWriteWord (sourceWriteWord (sourceWriteWord state (values + hole * 8) value)
        (order + position * 8) hole) (orderPos + hole * 8) position) := by
  have positionInside := Nat.lt_trans positionBound invariant.room
  have occupancy := invariant.delete_occupancy_separate state table keys stride capacity used values order orderPos count
    hole position bits holeInside positionInside
  have written := entries.write_value_layout32 state table keys stride capacity used values order orderPos count hole value bits
    invariant holeInside
  have orderSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → values + slot * 8 ≠ order + position * 8 := by
    intro slot inside
    have frames := invariant.delete_order_frames state table keys stride capacity used values order orderPos count slot bits inside
    exact Ne.symm (frames.2 position positionBound)
  have reverseSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → values + slot * 8 ≠ orderPos + hole * 8 := by
    intro slot inside
    have separate := invariant.value_reverse_separate state table keys stride capacity used values order orderPos count slot bits inside
    exact Ne.symm (separate hole holeInside)
  have ordered := written.after_word _ used values capacity (order + position * 8) hole
    (fun slot inside => (occupancy.2 slot inside).2.1) orderSeparate
  exact ordered.after_word _ used values capacity (orderPos + hole * 8) position
    (fun slot inside => (occupancy.2 slot inside).2.2) reverseSeparate

#print axioms HashValueEntriesWord.move_stores_layout32
end InitECandidate.Runtime
