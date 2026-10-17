import InitECandidate.Runtime.HashOrderLinkedInsert
import InitECandidate.Runtime.HashOrderCopyGeometryWidth
import InitECandidate.Runtime.HashReverseCopyGeometryWidth
import InitECandidate.Runtime.HashDeleteOccupancyGeometryWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The key-copy memory frame protects occupancy and both directions of the
live order link, even while the destination key bytes change. -/
theorem HashOrderLinked.copy_frame_layout_width {F : Type}
    (state post : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos items destinationSlot : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
    (linked : HashOrderLinked used order orderPos capacity items state)
    (inside : destinationSlot.toNat < capacity.toNat)
    (domain : post.memaddrs = state.memaddrs) (endian : post.be = state.be)
    (frame : ∀ cell : BitVec 64,
      (∀ offset : Nat, offset < keyLength.toNat → cell ≠ keys + destinationSlot * stride + BitVec.ofNat 64 offset) →
      (∀ offset : Nat, offset < keyLength.toNat → cell ≠ panByteAlignHOL (keys + destinationSlot * stride + BitVec.ofNat 64 offset)) →
      post.memory cell = state.memory cell) :
    HashOrderLinked used order orderPos capacity items post := by
  have occupancy := (invariant.delete_occupancy_separate_width state keyLength table keys stride capacity used values order orderPos items destinationSlot destinationSlot bits inside inside).1
  have reverse := invariant.delete_copy_reverse_separate_width state keyLength table keys stride capacity used values order orderPos items destinationSlot bits inside
  have forward := (invariant.delete_order_frames_width state keyLength table keys stride capacity used values order orderPos items destinationSlot bits inside).1
  apply linked.framed state post used order orderPos capacity items
  · intro slot bound occupied
    have cell := frame (panByteAlignHOL (used + slot))
      (fun offset small => (occupancy slot bound offset small).1)
      (fun offset small => (occupancy slot bound offset small).2)
    have same : hashOccupancyRead post used slot = hashOccupancyRead state used slot := by
      cases state
      cases post
      dsimp only at *
      subst_vars
      simp [hashOccupancyRead,panMemLoadByteHOL,cell]
    rw [← same]
    exact occupied
  · intro slot bound
    exact frame _ (fun offset small => (reverse slot bound offset small).1)
      (fun offset small => (reverse slot bound offset small).2)
  · intro position bound
    exact frame _ (fun offset small => (forward position bound offset small).1)
      (fun offset small => (forward position bound offset small).2)

#print axioms HashOrderLinked.copy_frame_layout_width
end InitECandidate.Runtime
