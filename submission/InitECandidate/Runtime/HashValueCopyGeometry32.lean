import InitECandidate.Runtime.HashValueCopyFrame
import InitECandidate.Runtime.HashDeleteCopyGeometry32
import InitECandidate.Runtime.HashDeleteOccupancyGeometry32
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Constructor/growth key-before-value ordering protects every value cell
from a deletion key copy, including its aligned byte writes. -/
theorem HashTableArraysInvariant32.delete_copy_values_separate {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count hole : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (holeInside : hole.toNat < capacity.toNat)
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat) :
    ∀ slot : BitVec 64, slot.toNat < capacity.toNat → ∀ offset : Nat, offset < 32 →
      values + slot * 8 ≠ keys + hole * stride + BitVec.ofNat 64 offset ∧
      values + slot * 8 ≠ panByteAlignHOL (keys + hole * stride + BitVec.ofNat 64 offset) := by
  intro slot inside
  exact invariant.delete_copy_separate state table keys stride capacity used values order orderPos count hole slot bits
    holeInside inside keysBeforeValues (values + slot * 8) (by simp)

theorem HashValueEntriesWord.copy_frame_layout32 {F : Type}
    (state post : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count hole : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (entries : HashValueEntriesWord used values capacity state)
    (holeInside : hole.toNat < capacity.toNat)
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (domain : post.memaddrs = state.memaddrs) (endian : post.be = state.be)
    (frame : ∀ cell : BitVec 64,
      (∀ offset : Nat, offset < 32 → cell ≠ keys + hole * stride + BitVec.ofNat 64 offset) →
      (∀ offset : Nat, offset < 32 → cell ≠ panByteAlignHOL (keys + hole * stride + BitVec.ofNat 64 offset)) →
      post.memory cell = state.memory cell) :
    HashValueEntriesWord used values capacity post := by
  have occupancy := invariant.delete_occupancy_separate state table keys stride capacity used values order orderPos count
    hole hole bits holeInside holeInside
  exact entries.copy_frame state post used values capacity (keys + hole * stride) 32 domain endian frame
    occupancy.1 (invariant.delete_copy_values_separate state table keys stride capacity used values order orderPos count hole bits
      holeInside keysBeforeValues)

#print axioms HashTableArraysInvariant32.delete_copy_values_separate
#print axioms HashValueEntriesWord.copy_frame_layout32
end InitECandidate.Runtime
