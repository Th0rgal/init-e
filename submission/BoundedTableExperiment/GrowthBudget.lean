import Init

namespace BoundedTableExperiment

/-- Capacity moved by `n` doublings from `base`, including the final capacity. -/
def capSum (base : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => capSum base n + base * 2 ^ n

/-- Total capacity copied over all doublings is at most the final capacity. -/
theorem capSum_le_final (base n : Nat) : capSum base n ≤ base * 2 ^ n := by
  induction n with
  | zero => simp [capSum]
  | succ n ih =>
      rw [capSum]
      have htwo : base * 2 ^ (n + 1) = 2 * (base * 2 ^ n) := by
        rw [Nat.pow_succ]
        rw [Nat.mul_comm (2 ^ n) 2, ← Nat.mul_assoc, Nat.mul_comm base 2]
        rw [Nat.mul_assoc]
      rw [htwo]
      omega

/-- A structural growth step moves at most twice the old live capacity. -/
theorem capSum_succ_le_two_mul_final (base n : Nat) :
    capSum base (n + 1) ≤ 2 * (base * 2 ^ n) := by
  have h := capSum_le_final base (n + 1)
  have htwo : base * 2 ^ (n + 1) = 2 * (base * 2 ^ n) := by
    rw [Nat.pow_succ]
    rw [Nat.mul_comm (2 ^ n) 2, ← Nat.mul_assoc, Nat.mul_comm base 2]
    rw [Nat.mul_assoc]
  rw [htwo] at h
  exact h

end BoundedTableExperiment

#print axioms BoundedTableExperiment.capSum_le_final
#print axioms BoundedTableExperiment.capSum_succ_le_two_mul_final
