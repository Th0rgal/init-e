import InitECandidate.Runtime.GasArithmetic
namespace InitECandidate.Runtime

/-- Source hash-table probing advances by a masked word increment. -/
def hashProbeNext (index capacity : BitVec 64) : BitVec 64 :=
  (index + 1) &&& (capacity - 1)

/-- Distance to a known empty slot in the cyclic probe order. -/
def hashProbeDistance (capacity index empty : Nat) : Nat :=
  if index ≤ empty then empty - index else capacity - index + empty

/-- Power-of-two capacity turns the actual source mask into modulo. -/
theorem hashProbeNext_toNat (index capacity : BitVec 64) (bits : Nat)
    (power : capacity.toNat = 2 ^ bits) (inside : index.toNat < capacity.toNat) :
    (hashProbeNext index capacity).toNat = (index.toNat + 1) % capacity.toNat := by
  have positive : 0 < capacity.toNat := by rw [power]; exact Nat.two_pow_pos bits
  have noWrap : index.toNat + 1 < 2 ^ 64 := by have := capacity.isLt; omega
  have oneLe : (1 : BitVec 64) ≤ capacity := BitVec.le_def.mpr (by change 1 ≤ capacity.toNat; omega)
  have decrement : (capacity - 1).toNat = capacity.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le oneLe]
    rfl
  simp only [hashProbeNext,BitVec.toNat_and,decrement,BitVec.toNat_add]
  have one : (1 : BitVec 64).toNat = 1 := rfl
  rw [one,Nat.mod_eq_of_lt noWrap,power,Nat.and_two_pow_sub_one_eq_mod]

/-- Every occupied slot strictly decreases distance to a known empty slot.
Thus a stable table with an empty slot cannot probe forever. -/
theorem hashProbeDistance_decreases (capacity index empty : Nat)
    (inside : index < capacity) (emptyInside : empty < capacity) (occupied : index ≠ empty) :
    hashProbeDistance capacity (if index + 1 < capacity then index + 1 else 0) empty <
      hashProbeDistance capacity index empty := by
  unfold hashProbeDistance
  split <;> split <;> split <;> omega

theorem hashProbeDistance_lt_capacity (capacity index empty : Nat)
    (inside : index < capacity) (emptyInside : empty < capacity) :
    hashProbeDistance capacity index empty < capacity := by
  unfold hashProbeDistance
  split <;> omega

theorem hashProbeNext_wrap (index capacity : BitVec 64) (bits : Nat)
    (power : capacity.toNat = 2 ^ bits) (inside : index.toNat < capacity.toNat) :
    (hashProbeNext index capacity).toNat =
      if index.toNat + 1 < capacity.toNat then index.toNat + 1 else 0 := by
  rw [hashProbeNext_toNat index capacity bits power inside]
  split
  · rename_i bounded
    exact Nat.mod_eq_of_lt bounded
  · rename_i wrapped
    have equal : index.toNat + 1 = capacity.toNat := by omega
    rw [equal,Nat.mod_self]

def hashProbeAdvance (capacity : BitVec 64) : Nat → BitVec 64 → BitVec 64
  | 0,index => index
  | steps + 1,index => hashProbeAdvance capacity steps (hashProbeNext index capacity)

/-- A power-of-two probe reaches any given empty slot in fewer than capacity
steps. The bound is uniform over starting hashes and includes wraparound. -/
theorem hashProbeAdvance_reaches (capacity empty : BitVec 64) (bits : Nat)
    (power : capacity.toNat = 2 ^ bits) (emptyInside : empty.toNat < capacity.toNat)
    (index : BitVec 64) (inside : index.toNat < capacity.toNat) :
    ∃ steps, steps ≤ hashProbeDistance capacity.toNat index.toNat empty.toNat ∧
      hashProbeAdvance capacity steps index = empty := by
  have positive : 0 < capacity.toNat := by rw [power]; exact Nat.two_pow_pos bits
  have visit : ∀ rank : Nat, ∀ current : BitVec 64, current.toNat < capacity.toNat →
      hashProbeDistance capacity.toNat current.toNat empty.toNat = rank →
      ∃ steps, steps ≤ rank ∧ hashProbeAdvance capacity steps current = empty := by
    intro rank
    induction rank using Nat.strongRecOn with
    | ind rank ih =>
      intro current bounded distance
      by_cases same : current = empty
      · exact ⟨0,by omega,by simp [hashProbeAdvance,same]⟩
      · have different : current.toNat ≠ empty.toNat := by
          intro equal; exact same (BitVec.eq_of_toNat_eq equal)
        have nextBounded : (hashProbeNext current capacity).toNat < capacity.toNat := by
          rw [hashProbeNext_toNat current capacity bits power bounded]
          exact Nat.mod_lt _ positive
        have decreases : hashProbeDistance capacity.toNat (hashProbeNext current capacity).toNat empty.toNat < rank := by
          rw [hashProbeNext_wrap current capacity bits power bounded,← distance]
          exact hashProbeDistance_decreases _ _ _ bounded emptyInside different
        obtain ⟨steps,limit,reaches⟩ := ih _ decreases _ nextBounded rfl
        exact ⟨steps + 1,by omega,reaches⟩
  exact visit _ index inside rfl

#print axioms hashProbeNext_wrap
#print axioms hashProbeAdvance_reaches
#print axioms hashProbeNext_toNat
#print axioms hashProbeDistance_decreases
#print axioms hashProbeDistance_lt_capacity
end InitECandidate.Runtime
