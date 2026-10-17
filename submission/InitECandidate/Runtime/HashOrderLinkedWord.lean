import InitECandidate.Runtime.HashOrderLinkedInsert
import InitECandidate.Runtime.HashOrderCopyGeometry32
import InitECandidate.Runtime.HashReverseValueGeometry32
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

theorem HashOrderLinked.after_word {F : Type} (state : PanSemStateFiniteExact 64 F)
    (used order orderPos capacity items destination value : BitVec 64)
    (linked : HashOrderLinked used order orderPos capacity items state)
    (occupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → panByteAlignHOL (used + slot) ≠ destination)
    (reverse : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → orderPos + slot * 8 ≠ destination)
    (forward : ∀ position : BitVec 64, position.toNat < items.toNat → order + position * 8 ≠ destination) :
    HashOrderLinked used order orderPos capacity items (sourceWriteWord state destination value) := by
  apply linked.framed state (sourceWriteWord state destination value) used order orderPos capacity items
  · intro slot inside occupied
    have same : hashOccupancyRead (sourceWriteWord state destination value) used slot = hashOccupancyRead state used slot := by
      simp [hashOccupancyRead,panMemLoadByteHOL,sourceWriteWord,occupancy slot inside]
      rfl
    rw [← same]
    exact occupied
  · intro slot inside
    change (if orderPos + slot * 8 = destination then HolWordLab.word value else _) = _
    rw [if_neg (reverse slot inside)]
  · intro position inside
    change (if order + position * 8 = destination then HolWordLab.word value else _) = _
    rw [if_neg (forward position inside)]

/-- Updating an existing value leaves both directions of the live order link intact. -/
theorem HashOrderLinked.write_value_layout32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos items slot value : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos items bits state)
    (linked : HashOrderLinked used order orderPos capacity items state)
    (inside : slot.toNat < capacity.toNat) :
    HashOrderLinked used order orderPos capacity items (sourceWriteWord state (values + slot * 8) value) := by
  have vu := invariant.valuesBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  have occupancy := hashSet_value_separate values used capacity slot inside invariant.valuesAligned invariant.usedAligned vu (by omega)
  have reverse := invariant.value_reverse_separate state table keys stride capacity used values order orderPos items slot bits inside
  have forward := (invariant.delete_order_frames state table keys stride capacity used values order orderPos items slot bits inside).2
  exact linked.after_word state used order orderPos capacity items (values + slot * 8) value occupancy reverse forward

#print axioms HashOrderLinked.after_word
#print axioms HashOrderLinked.write_value_layout32
end InitECandidate.Runtime
