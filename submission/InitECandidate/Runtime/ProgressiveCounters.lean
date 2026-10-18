import InitECandidate.Runtime.MerkleizeSource
namespace InitECandidate.Runtime

/-- The geometric chunk schedule and its counter envelope. -/
def ProgressiveCounters (n off size k : BitVec 64) : Prop :=
  off.toNat ≤ 4 * n.toNat ∧ size.toNat = 3 * off.toNat + 1 ∧ k.toNat ≤ off.toNat

theorem progressive_counters_initial (n : BitVec 64) : ProgressiveCounters n 0 1 0 := by
  simp [ProgressiveCounters]

/-- Every running iteration has natural, nonwrapping updates and strictly
decreases the remaining-input rank, even when its last chunk overshoots n. -/
theorem progressive_counters_step (n off size k : BitVec 64)
    (small : n.toNat ≤ 134217712) (valid : ProgressiveCounters n off size k)
    (running : off.toNat < n.toNat) :
    (off + size).toNat = off.toNat + size.toNat ∧
      (size <<< (2 : Nat)).toNat = size.toNat * 4 ∧
      (k + (1#64)).toNat = k.toNat + 1 ∧
      ProgressiveCounters n (off + size) (size <<< (2 : Nat)) (k + (1#64)) ∧
      n.toNat - (off + size).toNat < n.toNat - off.toNat := by
  obtain ⟨_,geometric,steps⟩ := valid
  have advance : off.toNat + size.toNat ≤ 4 * n.toNat := by omega
  have shifted : size.toNat * 4 ≤ 12 * n.toNat := by omega
  have nextK : k.toNat + 1 ≤ off.toNat + size.toNat := by omega
  have offNatural : (off + size).toNat = off.toNat + size.toNat := BitVec.toNat_add_of_lt (by omega)
  have sizeNatural : (size <<< (2 : Nat)).toNat = size.toNat * 4 := by
    rw [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
    exact Nat.mod_eq_of_lt (by omega)
  have kNatural : (k + (1#64)).toNat = k.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by change k.toNat + 1 < 2 ^ 64; omega)]
    rfl
  refine ⟨offNatural,sizeNatural,kNatural,?_,?_⟩
  · unfold ProgressiveCounters
    rw [offNatural,sizeNatural,kNatural]
    exact ⟨advance,by omega,nextK⟩
  · rw [offNatural]
    omega

def progressiveChunkCount (n off size : BitVec 64) : BitVec 64 :=
  if size < n - off then size else n - off

theorem progressive_chunk_bound (n off size : BitVec 64) (within : off.toNat ≤ n.toNat) :
    (progressiveChunkCount n off size).toNat ≤ n.toNat := by
  have remainder : (n - off).toNat = n.toNat - off.toNat := BitVec.toNat_sub_of_le (BitVec.le_def.mpr within)
  unfold progressiveChunkCount
  split
  · rename_i less
    have natural := BitVec.lt_def.mp less
    omega
  · rw [remainder]
    omega

#print axioms progressive_counters_initial
#print axioms progressive_counters_step
#print axioms progressive_chunk_bound
end InitECandidate.Runtime
