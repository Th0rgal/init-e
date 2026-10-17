import InitECandidate.Runtime.HashDeleteFinalOrderGeometryWidth
import InitECandidate.Runtime.HashDeleteOccupancyGeometryWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Allocation geometry supplies every separation premise used by the final
swap/count evaluator, independently of the occupancy change during clearing. -/
theorem HashTableArraysInvariant.delete_final_separation_width {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos items deletedPosition lastSlot : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
    (deletedInside : deletedPosition.toNat < items.toNat) (lastInside : lastSlot.toNat < capacity.toNat) :
    (∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ order + deletedPosition * 8 ∧
      panByteAlignHOL (used + slot) ≠ orderPos + lastSlot * 8 ∧ panByteAlignHOL (used + slot) ≠ table + 24) ∧
    (∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      orderPos + slot * 8 ≠ table + 24 ∧ (slot ≠ lastSlot →
        orderPos + slot * 8 ≠ order + deletedPosition * 8 ∧ orderPos + slot * 8 ≠ orderPos + lastSlot * 8)) ∧
    (∀ position : BitVec 64, position.toNat < items.toNat →
      order + position * 8 ≠ table + 24 ∧ (position ≠ deletedPosition →
        order + position * 8 ≠ order + deletedPosition * 8 ∧ order + position * 8 ≠ orderPos + lastSlot * 8)) ∧
    (order + deletedPosition * 8 ≠ orderPos + lastSlot * 8 ∧ order + deletedPosition * 8 ≠ table + 24) ∧
    orderPos + lastSlot * 8 ≠ table + 24 := by
  have positionInside := Nat.lt_trans deletedInside invariant.room
  have occupancy := (invariant.delete_occupancy_separate_width state keyLength table keys stride capacity used values order orderPos items lastSlot deletedPosition bits lastInside positionInside).2
  have facts := invariant.insertion_memory state keyLength table keys stride capacity used values order orderPos items bits
  have reverse := invariant.delete_reverse_separate_width state keyLength table keys stride capacity used values order orderPos items lastSlot deletedPosition bits lastInside positionInside
  have header : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → orderPos + slot * 8 ≠ table + 24 := by
    intro slot inside
    exact (invariant.insert_reverse_separation_width state keyLength table keys stride capacity used values order orderPos items slot bits inside).1
  obtain ⟨newForward,forward⟩ := invariant.delete_final_order_separation_width state keyLength table keys stride capacity used values order orderPos items deletedPosition lastSlot bits deletedInside lastInside
  refine ⟨?_,?_,forward,newForward,header lastSlot lastInside⟩
  · intro slot inside
    exact ⟨(occupancy slot inside).2.1,(occupancy slot inside).2.2,(facts.separate lastSlot lastInside slot inside).2.2⟩
  · intro slot inside
    exact ⟨header slot inside,reverse slot inside⟩

#print axioms HashTableArraysInvariant.delete_final_separation_width
end InitECandidate.Runtime
