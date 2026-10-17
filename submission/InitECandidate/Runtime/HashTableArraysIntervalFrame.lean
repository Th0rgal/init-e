import InitECandidate.Runtime.HashTableArraysHeaderFrame
import InitECandidate.Runtime.AllocationSeparation
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- An allocation interval frame preserves the invariant at every key width. -/
theorem HashTableArraysInvariant.interval_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (frame : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < orderPos.toNat + capacity.toNat * 8 → post.memory address = state.memory address)
    (code : post.code = state.code) (domain : post.memaddrs = state.memaddrs) (endian : post.be = state.be) :
    HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits post := by
  have hv := invariant.headerValues
  have vu := invariant.valuesBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  apply invariant.framed state post keyLength table keys stride capacity used values order orderPos count bits
  · intro offset member
    have small : offset ≤ 64 := by simp at member; omega
    have natural : (BitVec.ofNat 64 offset).toNat = offset := by
      change offset % 2 ^ 64 = offset
      exact Nat.mod_eq_of_lt (by omega)
    have address : (table + BitVec.ofNat 64 offset).toNat = table.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    apply frame <;> omega
  · intro slot inside
    have interval := hashOccupancy_aligned_interval used capacity slot invariant.usedAligned (by omega) inside
    have cell := frame (panByteAlignHOL (used + slot)) (by omega) (by omega)
    simp only [hashOccupancyRead,panMemLoadByteHOL,endian,cell]
    rw [domain]
  · exact code
  · exact domain

#print axioms HashTableArraysInvariant.interval_frame
end InitECandidate.Runtime
