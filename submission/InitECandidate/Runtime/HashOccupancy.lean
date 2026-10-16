import InitECandidate.Runtime.HashProbeLoop
import Init.Data.List.Count
namespace InitECandidate.Runtime

/-- Count nonempty occupancy slots. Failed byte reads count as nonempty, so
this definition never invents an empty slot from an inaccessible address. -/
def hashOccupiedCount (capacity : BitVec 64) (read : BitVec 64 → Option UInt8) : Nat :=
  (List.range capacity.toNat).countP (fun index => read (BitVec.ofNat 64 index) != some 0)

/-- A load-factor invariant strictly below capacity supplies an actual readable
empty byte, eliminating an independent empty-slot assumption at probe sites. -/
theorem hashOccupiedCount_exists_empty (capacity : BitVec 64)
    (read : BitVec 64 → Option UInt8) (room : hashOccupiedCount capacity read < capacity.toNat) :
    ∃ empty : BitVec 64, empty.toNat < capacity.toNat ∧ read empty = some 0 := by
  classical
  apply Classical.byContradiction
  intro missing
  have full : ∀ index ∈ List.range capacity.toNat,
      (read (BitVec.ofNat 64 index) != some 0) = true := by
    intro index member
    have bounded : index < capacity.toNat := List.mem_range.mp member
    have wordBound : index < 2 ^ 64 := Nat.lt_trans bounded capacity.isLt
    have notEmpty : read (BitVec.ofNat 64 index) ≠ some 0 := by
      intro empty
      apply missing
      exact ⟨BitVec.ofNat 64 index,by simpa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt wordBound] using bounded,empty⟩
    simp [notEmpty]
  have count : hashOccupiedCount capacity read = capacity.toNat := by
    unfold hashOccupiedCount
    rw [List.countP_eq_length.mpr full,List.length_range]
  omega

#print axioms hashOccupiedCount_exists_empty
end InitECandidate.Runtime
