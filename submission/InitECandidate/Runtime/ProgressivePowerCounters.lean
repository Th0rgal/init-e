import InitECandidate.Runtime.ProgressiveCounters
namespace InitECandidate.Runtime

/-- The actual geometric schedule, including the root index that determines
which cell of the fixed 24-root allocation receives each Merkle result. -/
def ProgressivePowerCounters (n off size k : BitVec 64) : Prop :=
  ProgressiveCounters n off size k ∧ size.toNat = 4 ^ k.toNat

theorem progressive_power_counters_initial (n : BitVec 64) : ProgressivePowerCounters n 0 1 0 := by
  exact ⟨progressive_counters_initial n,by decide⟩

theorem progressive_power_counters_step (n off size k : BitVec 64)
    (small : n.toNat ≤ 134217712) (valid : ProgressivePowerCounters n off size k)
    (running : off.toNat < n.toNat) :
    ProgressivePowerCounters n (off + size) (size <<< (2 : Nat)) (k + (1#64)) := by
  have facts := progressive_counters_step n off size k small valid.1 running
  refine ⟨facts.2.2.2.1,?_⟩
  rw [facts.2.1,facts.2.2.1,valid.2,Nat.pow_succ]

/-- The checked input-size ceiling prevents the actual root index from
reaching the end of the source's fixed 24-root buffer, even at loop exit. -/
theorem progressive_power_root_index (n off size k : BitVec 64)
    (small : n.toNat ≤ 134217712) (valid : ProgressivePowerCounters n off size k) :
    k.toNat < 24 := by
  by_contra outside
  have lower : 4 ^ 24 ≤ 4 ^ k.toNat := Nat.pow_le_pow_right (by decide) (by omega)
  have sizeBound : size.toNat ≤ 12 * n.toNat + 1 := by
    obtain ⟨envelope,geometric,_⟩ := valid.1
    omega
  rw [← valid.2] at lower
  norm_num at lower
  omega

/-- Every actual progressive output word is aligned and its full SHA output
lies inside the checked 768-byte root allocation. -/
theorem progressive_root_output_geometry (roots k : BitVec 64)
    (index : k.toNat < 24) (aligned : roots.toNat % 8 = 0)
    (fits : roots.toNat + 768 ≤ 33806089496) :
    (roots + k * (32#64)).toNat = roots.toNat + k.toNat * 32 ∧
      (roots + k * (32#64)).toNat % 8 = 0 ∧
      (roots + k * (32#64)).toNat + 32 ≤ 33806089496 := by
  have multiplied : (k * (32#64)).toNat = k.toNat * 32 := by
    apply BitVec.toNat_mul_of_lt
    change k.toNat * 32 < 2 ^ 64
    omega
  have natural : (roots + k * (32#64)).toNat = roots.toNat + k.toNat * 32 := by
    rw [BitVec.toNat_add_of_lt (by rw [multiplied]; omega),multiplied]
  refine ⟨natural,?_,by rw [natural]; omega⟩
  rw [natural,Nat.add_mod,Nat.mul_mod,aligned]
  simp

#print axioms progressive_power_counters_initial
#print axioms progressive_power_counters_step
#print axioms progressive_power_root_index
#print axioms progressive_root_output_geometry
end InitECandidate.Runtime
