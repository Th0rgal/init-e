import InitECandidate.Runtime.HashOccupancy
namespace InitECandidate.Runtime

/-- Filling one previously empty slot increases the finite occupancy count
by exactly one. The slot is in range, so it occurs exactly once. -/
theorem hash_countP_fill (occupied : Nat → Bool) (capacity slot : Nat)
    (inside : slot < capacity) (empty : occupied slot = false) :
    (List.range capacity).countP (fun index => if index = slot then true else occupied index) =
      (List.range capacity).countP occupied + 1 := by
  induction capacity with
  | zero => omega
  | succ capacity ih =>
    rw [List.range_succ,List.countP_append,List.countP_append]
    by_cases last : slot = capacity
    · subst slot
      have before : (List.range capacity).countP
          (fun index => if index = capacity then true else occupied index) =
            (List.range capacity).countP occupied := by
        apply List.countP_congr
        intro index member
        have different : index ≠ capacity := by have := List.mem_range.mp member; omega
        simp [different]
      rw [before]
      simp [empty]
    · have bounded : slot < capacity := by omega
      have backwards : capacity ≠ slot := Ne.symm last
      rw [ih bounded]
      simp [backwards]
      omega

/-- Apply the count update to word-indexed occupancy reads. A byte-store
proof can discharge the single-slot change and preservation premises. -/
theorem hashOccupiedCount_fill (capacity slot : BitVec 64)
    (before after : BitVec 64 → Option UInt8) (inside : slot.toNat < capacity.toNat)
    (empty : before slot = some 0) (filled : after slot ≠ some 0)
    (unchanged : ∀ index, index ≠ slot → after index = before index) :
    hashOccupiedCount capacity after = hashOccupiedCount capacity before + 1 := by
  classical
  let occupied := fun index : Nat => before (BitVec.ofNat 64 index) != some 0
  have emptyAt : occupied slot.toNat = false := by
    simp [occupied,empty]
  have count := hash_countP_fill occupied capacity.toNat slot.toNat inside emptyAt
  have same : (List.range capacity.toNat).countP
      (fun index => after (BitVec.ofNat 64 index) != some 0) =
      (List.range capacity.toNat).countP
        (fun index => if index = slot.toNat then true else occupied index) := by
    apply List.countP_congr
    intro index member
    have bound : index < 2 ^ 64 := Nat.lt_trans (List.mem_range.mp member) capacity.isLt
    by_cases equal : index = slot.toNat
    · subst index
      simp [filled]
    · have wordsDifferent : BitVec.ofNat 64 index ≠ slot := by
        intro wordsEqual
        have numbersEqual := congrArg BitVec.toNat wordsEqual
        apply equal
        simpa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound] using numbersEqual
      rw [unchanged _ wordsDifferent]
      simp [equal,occupied]
  exact same.trans count

#print axioms hashOccupiedCount_fill
#print axioms hash_countP_fill
end InitECandidate.Runtime
