import InitECandidate.Runtime.HashTableArraysHeaderFrame32
import InitECandidate.Runtime.HashDeleteOccupancyGeometry32
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A copy into a bounded key slot preserves the table header and occupancy layout. -/
theorem HashTableArraysInvariant32.key_copy_frame {F : Type}
    (state post : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count hole : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (inside : hole.toNat < capacity.toNat)
    (code : post.code = state.code) (domain : post.memaddrs = state.memaddrs) (endian : post.be = state.be)
    (frame : ∀ cell : BitVec 64,
      (∀ offset : Nat, offset < 32 → cell ≠ keys + hole * stride + BitVec.ofNat 64 offset) →
      (∀ offset : Nat, offset < 32 → cell ≠ panByteAlignHOL (keys + hole * stride + BitVec.ofNat 64 offset)) →
      post.memory cell = state.memory cell) :
    HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits post := by
  have headers := invariant.key_copy_header_separate state table keys stride capacity used values order orderPos count hole bits inside
  have occupancy := (invariant.delete_occupancy_separate state table keys stride capacity used values order orderPos count hole hole bits inside inside).1
  apply invariant.framed state post table keys stride capacity used values order orderPos count bits ?_ ?_ code domain
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

#print axioms HashTableArraysInvariant32.key_copy_frame
end InitECandidate.Runtime
