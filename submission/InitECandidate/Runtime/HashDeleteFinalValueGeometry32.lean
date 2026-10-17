import InitECandidate.Runtime.HashDeleteFinalSeparation32
import InitECandidate.Runtime.HashValueMoveGeometry32
import InitECandidate.Runtime.HashReverseValueGeometry32
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

theorem HashTableArraysInvariant32.delete_final_value_separation {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos items deletedPosition lastSlot : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos items bits state)
    (deletedInside : deletedPosition.toNat < items.toNat) (lastInside : lastSlot.toNat < capacity.toNat) :
    ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      values + slot * 8 ≠ order + deletedPosition * 8 ∧
      values + slot * 8 ≠ orderPos + lastSlot * 8 ∧ values + slot * 8 ≠ table + 24 := by
  have facts := invariant.insertion_memory state table keys stride capacity used values order orderPos items bits
  intro slot inside
  exact ⟨Ne.symm ((invariant.delete_order_frames state table keys stride capacity used values order orderPos items slot bits inside).2 deletedPosition deletedInside),
    Ne.symm (invariant.value_reverse_separate state table keys stride capacity used values order orderPos items slot bits inside lastSlot lastInside),
    Ne.symm (facts.valueCountSeparate slot inside)⟩

#print axioms HashTableArraysInvariant32.delete_final_value_separation
end InitECandidate.Runtime
