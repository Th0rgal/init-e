import InitECandidate.Runtime.AllocationSeparation
namespace InitECandidate.Runtime
open Flapjack

/-- An aligned, heap-bounded copy cannot change a word outside its natural
byte interval, through either full-word or aligned-byte store addresses. -/
theorem memcpy_interval_separate (destination size watched : BitVec 64)
    (aligned : destination.toNat % 8 = 0)
    (bounded : destination.toNat + size.toNat ≤ 33806089496)
    (outside : watched.toNat < destination.toNat ∨ destination.toNat + size.toNat ≤ watched.toNat) :
    ∀ offset : Nat, offset < size.toNat →
      watched ≠ destination + BitVec.ofNat 64 offset ∧
      watched ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset) := by
  intro offset inside
  have small : offset < 2 ^ 64 := Nat.lt_trans inside size.isLt
  have natural : (BitVec.ofNat 64 offset).toNat = offset := by
    change offset % 2 ^ 64 = offset
    exact Nat.mod_eq_of_lt small
  have sumSmall : destination.toNat + (BitVec.ofNat 64 offset).toNat < 2 ^ 64 := by rw [natural]; omega
  have address := BitVec.toNat_add_of_lt sumSmall
  rw [natural] at address
  have cell := hashOccupancy_aligned_interval destination size (BitVec.ofNat 64 offset) aligned (by omega)
    (by rw [natural]; exact inside)
  constructor
  · intro same
    have equal := congrArg BitVec.toNat same
    rw [address] at equal
    omega
  · intro same
    have equal := congrArg BitVec.toNat same
    omega

/-- Header fields before a copied key slot and occupancy after it are outside
all actual copy-store cells. These are the three words insertion must retain. -/
theorem hashInsert_copy_watched_separate (table destination size used capacity index : BitVec 64)
    (inside : index.toNat < capacity.toNat)
    (destinationAligned : destination.toNat % 8 = 0) (usedAligned : used.toNat % 8 = 0)
    (headerBefore : table.toNat + 72 ≤ destination.toNat)
    (copyBefore : destination.toNat + size.toNat ≤ used.toNat)
    (bounded : used.toNat + capacity.toNat ≤ 33806089496) :
    ∀ watched ∈ ([table + 40,table + 24,panByteAlignHOL (used + index)] : List (BitVec 64)),
      ∀ offset : Nat, offset < size.toNat →
        watched ≠ destination + BitVec.ofNat 64 offset ∧
        watched ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset) := by
  have header : ∀ offset : Nat, offset ≤ 64 → (table + BitVec.ofNat 64 offset).toNat < destination.toNat := by
    intro offset small
    have offsetNat : (BitVec.ofNat 64 offset).toNat = offset := by
      change offset % 2 ^ 64 = offset
      exact Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_add_of_lt (by rw [offsetNat]; omega),offsetNat]
    omega
  have occupancy := hashOccupancy_aligned_interval used capacity index usedAligned (by omega) inside
  intro watched member
  apply memcpy_interval_separate destination size watched destinationAligned (by omega)
  simp at member
  rcases member with rfl | rfl | rfl
  · exact Or.inl (header 40 (by decide))
  · exact Or.inl (header 24 (by decide))
  · exact Or.inr (by omega)

#print axioms memcpy_interval_separate
#print axioms hashInsert_copy_watched_separate
end InitECandidate.Runtime
