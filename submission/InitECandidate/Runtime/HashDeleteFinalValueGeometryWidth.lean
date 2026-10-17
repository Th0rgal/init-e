import InitECandidate.Runtime.HashDeleteFinalSeparationWidth
import InitECandidate.Runtime.HashOrderCopyGeometryWidth
import InitECandidate.Runtime.HashReverseValueGeometryWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

theorem HashTableArraysInvariant.delete_final_value_separation_width {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos items deletedPosition lastSlot : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
    (deletedInside : deletedPosition.toNat < items.toNat) (lastInside : lastSlot.toNat < capacity.toNat) :
    ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      values + slot * 8 ≠ order + deletedPosition * 8 ∧
      values + slot * 8 ≠ orderPos + lastSlot * 8 ∧ values + slot * 8 ≠ table + 24 := by
  have facts := invariant.insertion_memory state keyLength table keys stride capacity used values order orderPos items bits
  intro slot inside
  exact ⟨Ne.symm ((invariant.delete_order_frames_width state keyLength table keys stride capacity used values order orderPos items slot bits inside).2 deletedPosition deletedInside),
    Ne.symm (invariant.value_reverse_separate_width state keyLength table keys stride capacity used values order orderPos items slot bits inside lastSlot lastInside),
    Ne.symm (facts.valueCountSeparate slot inside)⟩

#print axioms HashTableArraysInvariant.delete_final_value_separation_width
end InitECandidate.Runtime
