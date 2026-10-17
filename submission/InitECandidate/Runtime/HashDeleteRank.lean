import InitECandidate.Runtime.HashDeleteLoopSource
namespace InitECandidate.Runtime

/-- Remaining deletion iterations, including the iteration that discovers an empty slot. -/
def hashDeleteRank (capacity index empty : BitVec 64) : Nat :=
  hashProbeDistance capacity.toNat (hashProbeNext index capacity).toNat empty.toNat + 1

theorem hashDeleteRank_bounded (capacity index empty : BitVec 64) (bits : Nat)
    (power : capacity.toNat = 2 ^ bits) (inside : index.toNat < capacity.toNat)
    (emptyInside : empty.toNat < capacity.toNat) :
    0 < hashDeleteRank capacity index empty ∧ hashDeleteRank capacity index empty ≤ capacity.toNat := by
  have positive : 0 < capacity.toNat := by rw [power]; exact Nat.two_pow_pos bits
  have nextInside : (hashProbeNext index capacity).toNat < capacity.toNat := by
    rw [hashProbeNext_toNat index capacity bits power inside]
    exact Nat.mod_lt _ positive
  have bound := hashProbeDistance_lt_capacity capacity.toNat (hashProbeNext index capacity).toNat empty.toNat nextInside emptyInside
  unfold hashDeleteRank
  omega

/-- Occupied iterations advance the scan while retaining the empty slot,
so their remaining rank strictly decreases even when the hole moves. -/
theorem hashDeleteRank_decreases (capacity index empty : BitVec 64) (bits : Nat)
    (power : capacity.toNat = 2 ^ bits) (inside : index.toNat < capacity.toNat)
    (emptyInside : empty.toNat < capacity.toNat)
    (different : hashProbeNext index capacity ≠ empty) :
    hashDeleteRank capacity (hashProbeNext index capacity) empty < hashDeleteRank capacity index empty := by
  have positive : 0 < capacity.toNat := by rw [power]; exact Nat.two_pow_pos bits
  have nextInside : (hashProbeNext index capacity).toNat < capacity.toNat := by
    rw [hashProbeNext_toNat index capacity bits power inside]
    exact Nat.mod_lt _ positive
  have natural : (hashProbeNext index capacity).toNat ≠ empty.toNat :=
    fun same => different (BitVec.eq_of_toNat_eq same)
  unfold hashDeleteRank
  rw [hashProbeNext_wrap (hashProbeNext index capacity) capacity bits power nextInside]
  have decrease := hashProbeDistance_decreases capacity.toNat (hashProbeNext index capacity).toNat empty.toNat nextInside emptyInside natural
  omega

theorem hashDeleteRank_terminal (capacity index empty : BitVec 64)
    (same : hashProbeNext index capacity = empty) : hashDeleteRank capacity index empty = 1 := by
  simp [hashDeleteRank,same,hashProbeDistance]

#print axioms hashDeleteRank_bounded
#print axioms hashDeleteRank_decreases
#print axioms hashDeleteRank_terminal
end InitECandidate.Runtime
