import InitECandidate.Runtime.HashTableArraysHeaderFrame
import InitECandidate.Runtime.HashDeleteOccupancyGeometryWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

theorem HashTableArraysInvariant.key_copy_header_separate_width {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count hole : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (inside : hole.toNat < capacity.toNat) :
    ∀ headerOffset : Nat, headerOffset ≤ 64 → ∀ offset : Nat, offset < keyLength.toNat →
      table + BitVec.ofNat 64 headerOffset ≠ keys + hole * stride + BitVec.ofNat 64 offset ∧
      table + BitVec.ofNat 64 headerOffset ≠ panByteAlignHOL (keys + hole * stride + BitVec.ofNat 64 offset) := by
  have hk := invariant.headerKeys
  have ku := invariant.keysBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  have keyAddress := (hashFind_slot_address keys hole stride capacity inside (by omega) invariant.keysAligned invariant.strideAligned)
  have fits := invariant.fits
  have next := Nat.mul_le_mul_right stride.toNat (show hole.toNat + 1 ≤ capacity.toNat by omega)
  rw [Nat.add_mul,Nat.one_mul] at next
  have copyBound : (keys + hole * stride).toNat + keyLength.toNat ≤ 33806089496 := by
    rw [keyAddress.1]
    omega
  intro headerOffset small offset inRange
  have natural : (BitVec.ofNat 64 headerOffset).toNat = headerOffset := by
    change headerOffset % 2 ^ 64 = headerOffset
    exact Nat.mod_eq_of_lt (by omega)
  have headerAddress : (table + BitVec.ofNat 64 headerOffset).toNat = table.toNat + headerOffset := by
    rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
  exact memcpy_interval_separate (keys + hole * stride) keyLength (table + BitVec.ofNat 64 headerOffset)
    keyAddress.2 copyBound (Or.inl (by rw [headerAddress,keyAddress.1]; omega)) offset inRange


theorem HashTableArraysInvariant.key_copy_frame_width {F : Type}
    (state post : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count hole : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (inside : hole.toNat < capacity.toNat)
    (code : post.code = state.code) (domain : post.memaddrs = state.memaddrs) (endian : post.be = state.be)
    (frame : ∀ cell : BitVec 64,
      (∀ offset : Nat, offset < keyLength.toNat → cell ≠ keys + hole * stride + BitVec.ofNat 64 offset) →
      (∀ offset : Nat, offset < keyLength.toNat → cell ≠ panByteAlignHOL (keys + hole * stride + BitVec.ofNat 64 offset)) →
      post.memory cell = state.memory cell) :
    HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits post := by
  have headers := invariant.key_copy_header_separate_width state keyLength table keys stride capacity used values order orderPos count hole bits inside
  have occupancy := (invariant.delete_occupancy_separate_width state keyLength table keys stride capacity used values order orderPos count hole hole bits inside inside).1
  apply invariant.framed state post keyLength table keys stride capacity used values order orderPos count bits ?_ ?_ code domain
  · intro headerOffset member
    have small : headerOffset ≤ 64 := by simp at member; omega
    exact frame _ (fun offset bound => (headers headerOffset small offset bound).1)
      (fun offset bound => (headers headerOffset small offset bound).2)
  · intro slot bound
    have cell := frame (panByteAlignHOL (used + slot))
      (fun offset small => (occupancy slot bound offset small).1)
      (fun offset small => (occupancy slot bound offset small).2)
    cases state
    cases post
    dsimp only at *
    subst_vars
    simp [hashOccupancyRead,panMemLoadByteHOL,cell]

#print axioms HashTableArraysInvariant.key_copy_header_separate_width
#print axioms HashTableArraysInvariant.key_copy_frame_width
end InitECandidate.Runtime
