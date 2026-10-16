import InitECandidate.Runtime.HashDeleteCopyGeometry32
import InitECandidate.Runtime.HashSetExisting
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

theorem HashTableArraysInvariant32.delete_occupancy_separate {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count hole position : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (holeInside : hole.toNat < capacity.toNat) (positionInside : position.toNat < capacity.toNat) :
    (∀ slot : BitVec 64, slot.toNat < capacity.toNat → ∀ offset : Nat, offset < 32 →
      panByteAlignHOL (used + slot) ≠ keys + hole * stride + BitVec.ofNat 64 offset ∧
      panByteAlignHOL (used + slot) ≠ panByteAlignHOL (keys + hole * stride + BitVec.ofNat 64 offset)) ∧
    (∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ values + hole * 8 ∧
      panByteAlignHOL (used + slot) ≠ order + position * 8 ∧
      panByteAlignHOL (used + slot) ≠ orderPos + hole * 8) := by
  have ku := invariant.keysBefore
  have vu := invariant.valuesBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have limit := invariant.endBound
  have keyAddress := hashFind_slot_address keys hole stride capacity holeInside (by omega)
    invariant.keysAligned invariant.strideAligned
  have next : (hole.toNat + 1) * stride.toNat ≤ capacity.toNat * stride.toNat :=
    Nat.mul_le_mul_right stride.toNat (by omega)
  rw [Nat.add_mul,Nat.one_mul] at next
  have fits := invariant.fits
  have copyBefore : (keys + hole * stride).toNat + 32 ≤ used.toNat := by rw [keyAddress.1]; omega
  have copy := memcpy_occupancy_separate (keys + hole * stride) 32 used capacity keyAddress.2
    invariant.usedAligned copyBefore (by omega)
  have value := hashSet_value_separate values used capacity hole holeInside invariant.valuesAligned
    invariant.usedAligned vu (by omega)
  have orderAddress := (hashFind_slot_address order position 8 capacity positionInside
    (by change order.toNat + capacity.toNat * 8 ≤ 33806089496; omega) invariant.orderAligned (by decide)).1
  have reverseAddress := (hashFind_slot_address orderPos hole 8 capacity holeInside
    (by change orderPos.toNat + capacity.toNat * 8 ≤ 33806089496; omega) invariant.orderPosAligned (by decide)).1
  change (order + position * 8).toNat = order.toNat + position.toNat * 8 at orderAddress
  change (orderPos + hole * 8).toNat = orderPos.toNat + hole.toNat * 8 at reverseAddress
  have orderSeparate := hashOccupancy_separate_allocation used capacity (order + position * 8)
    invariant.usedAligned (by omega) (Or.inr (by omega))
  have reverseSeparate := hashOccupancy_separate_allocation used capacity (orderPos + hole * 8)
    invariant.usedAligned (by omega) (Or.inr (by omega))
  exact ⟨fun slot inside offset bound => copy offset bound slot inside,
    fun slot inside => ⟨value slot inside,orderSeparate slot inside,reverseSeparate slot inside⟩⟩

#print axioms HashTableArraysInvariant32.delete_occupancy_separate
end InitECandidate.Runtime
