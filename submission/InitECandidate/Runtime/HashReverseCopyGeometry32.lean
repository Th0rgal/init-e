import InitECandidate.Runtime.HashDeleteCopyGeometry32
import InitECandidate.Runtime.HashReverseEntriesBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Every reverse cell lies after the key-copy interval. This does not need
key/value ordering: occupancy separates keys from the reverse array. -/
theorem HashTableArraysInvariant32.delete_copy_reverse_separate {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count hole : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (holeInside : hole.toNat < capacity.toNat) :
    ∀ slot : BitVec 64, slot.toNat < capacity.toNat → ∀ offset : Nat, offset < 32 →
      orderPos + slot * 8 ≠ keys + hole * stride + BitVec.ofNat 64 offset ∧
      orderPos + slot * 8 ≠ panByteAlignHOL (keys + hole * stride + BitVec.ofNat 64 offset) := by
  have ku := invariant.keysBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  have keyAddress := hashFind_slot_address keys hole stride capacity holeInside (by omega)
    invariant.keysAligned invariant.strideAligned
  have next := Nat.mul_le_mul_right stride.toNat (show hole.toNat + 1 ≤ capacity.toNat by omega)
  rw [Nat.add_mul,Nat.one_mul] at next
  have fits := invariant.fits
  have copyBefore : (keys + hole * stride).toNat + 32 ≤ used.toNat := by rw [keyAddress.1]; omega
  intro slot inside offset bound
  have reverseAddress := (hashFind_slot_address orderPos slot 8 capacity inside
    (by change orderPos.toNat + capacity.toNat * 8 ≤ 33806089496; exact bounded)
    invariant.orderPosAligned (by decide)).1
  change (orderPos + slot * 8).toNat = orderPos.toNat + slot.toNat * 8 at reverseAddress
  exact memcpy_interval_separate (keys + hole * stride) 32 (orderPos + slot * 8) keyAddress.2
    (by change (keys + hole * stride).toNat + 32 ≤ 33806089496; omega)
    (Or.inr (by change (keys + hole * stride).toNat + 32 ≤ (orderPos + slot * 8).toNat; omega))
    offset (by change offset < 32; exact bound)

#print axioms HashTableArraysInvariant32.delete_copy_reverse_separate
end InitECandidate.Runtime
