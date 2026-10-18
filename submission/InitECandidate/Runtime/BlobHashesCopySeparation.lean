import InitECandidate.Runtime.AllocationSeparation
namespace InitECandidate.Runtime
open Flapjack

/-- An aligned blob output starts after every protected word below the buffer;
all 32 bytes of an enabled output slot keep that separation. -/
theorem blobHashes_copy_cells_after_buffer (buffer index watched : BitVec 64)
    (aligned : buffer.toNat % 8 = 0)
    (fits : buffer.toNat + index.toNat * 32 + 32 ≤ 2^64)
    (below : watched.toNat < buffer.toNat) (offset : Nat) (inside : offset < 32) :
    watched ≠ (buffer + index * 32) + BitVec.ofNat 64 offset ∧
    watched ≠ panByteAlignHOL ((buffer + index * 32) + BitVec.ofNat 64 offset) := by
  have product : (index * 32).toNat = index.toNat * 32 := by
    change (index.toNat * 32) % 2^64 = index.toNat * 32
    apply Nat.mod_eq_of_lt
    omega
  have destination : (buffer + index * 32).toNat = buffer.toNat + index.toNat * 32 := by
    rw [BitVec.toNat_add_of_lt (by rw [product]; omega),product]
  have offsetNat : (BitVec.ofNat 64 offset).toNat = offset := by
    change offset % 2^64 = offset
    apply Nat.mod_eq_of_lt
    omega
  have address : ((buffer + index * 32) + BitVec.ofNat 64 offset).toNat = buffer.toNat + index.toNat * 32 + offset := by
    rw [BitVec.toNat_add_of_lt (by rw [destination,offsetNat]; omega),destination,offsetNat]
  constructor
  · intro equal
    have same := congrArg BitVec.toNat equal
    rw [address] at same
    omega
  · intro equal
    have same := congrArg BitVec.toNat equal
    rw [panByteAlign_toNat64,address] at same
    have original := Nat.mod_add_div buffer.toNat 8
    have current := Nat.mod_add_div (buffer.toNat + index.toNat * 32 + offset) 8
    have remainder := Nat.mod_lt (buffer.toNat + index.toNat * 32 + offset) (by decide : 0 < 8)
    omega

#print axioms blobHashes_copy_cells_after_buffer
end InitECandidate.Runtime
