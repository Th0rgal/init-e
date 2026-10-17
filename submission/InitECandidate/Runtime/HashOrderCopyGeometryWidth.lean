import InitECandidate.Runtime.HashDeleteCopyGeometryWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Live forward-order cells lie beyond both key-copy and value-write regions. -/
theorem HashTableArraysInvariant.delete_order_frames_width {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count hole : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (holeInside : hole.toNat < capacity.toNat) :
    (∀ index : BitVec 64, index.toNat < count.toNat → ∀ offset : Nat, offset < keyLength.toNat →
      order + index * 8 ≠ keys + hole * stride + BitVec.ofNat 64 offset ∧
      order + index * 8 ≠ panByteAlignHOL (keys + hole * stride + BitVec.ofNat 64 offset)) ∧
    (∀ index : BitVec 64, index.toNat < count.toNat → order + index * 8 ≠ values + hole * 8) := by
  have ku := invariant.keysBefore
  have vu := invariant.valuesBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  have room := invariant.room
  have keyAddress := hashFind_slot_address keys hole stride capacity holeInside (by omega)
    invariant.keysAligned invariant.strideAligned
  have next := Nat.mul_le_mul_right stride.toNat (show hole.toNat + 1 ≤ capacity.toNat by omega)
  rw [Nat.add_mul,Nat.one_mul] at next
  have fits := invariant.fits
  have copyBefore : (keys + hole * stride).toNat + keyLength.toNat ≤ used.toNat := by rw [keyAddress.1]; omega
  have orderAddress : ∀ index : BitVec 64, index.toNat < count.toNat →
      (order + index * 8).toNat = order.toNat + index.toNat * 8 := by
    intro index inside
    exact (hashFind_slot_address order index 8 capacity (by omega)
      (by change order.toNat + capacity.toNat * 8 ≤ 33806089496; omega)
      invariant.orderAligned (by decide)).1
  have valueAddress := (hashFind_slot_address values hole 8 capacity holeInside
    (by change values.toNat + capacity.toNat * 8 ≤ 33806089496; omega)
    invariant.valuesAligned (by decide)).1
  change (values + hole * 8).toNat = values.toNat + hole.toNat * 8 at valueAddress
  have product := Nat.mul_lt_mul_of_pos_right holeInside (by decide : 0 < 8)
  constructor
  · intro index inside offset bound
    have address := orderAddress index inside
    exact memcpy_interval_separate (keys + hole * stride) keyLength (order + index * 8) keyAddress.2
      (by change (keys + hole * stride).toNat + keyLength.toNat ≤ 33806089496; omega)
      (Or.inr (by change (keys + hole * stride).toNat + keyLength.toNat ≤ (order + index * 8).toNat; omega))
      offset (by change offset < keyLength.toNat; exact bound)
  · intro index inside same
    have natural := congrArg BitVec.toNat same
    rw [orderAddress index inside,valueAddress] at natural
    omega

#print axioms HashTableArraysInvariant.delete_order_frames_width
end InitECandidate.Runtime
