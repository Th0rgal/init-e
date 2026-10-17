import InitECandidate.Runtime.HashOrderLinkedWord
import InitECandidate.Runtime.HashOrderCopyGeometryWidth
import InitECandidate.Runtime.HashReverseValueGeometryWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

theorem HashOrderLinked.write_value_layout_width {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos items slot value : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
    (linked : HashOrderLinked used order orderPos capacity items state)
    (inside : slot.toNat < capacity.toNat) :
    HashOrderLinked used order orderPos capacity items (sourceWriteWord state (values + slot * 8) value) := by
  have vu := invariant.valuesBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  have occupancy := hashSet_value_separate values used capacity slot inside invariant.valuesAligned invariant.usedAligned vu (by omega)
  have reverse := invariant.value_reverse_separate_width state keyLength table keys stride capacity used values order orderPos items slot bits inside
  have forward := (invariant.delete_order_frames_width state keyLength table keys stride capacity used values order orderPos items slot bits inside).2
  exact linked.after_word state used order orderPos capacity items (values + slot * 8) value occupancy reverse forward

#print axioms HashOrderLinked.write_value_layout_width
end InitECandidate.Runtime
