import InitECandidate.Runtime.ArenaBoundary
/-!
The actual source memory domain `ordinaryDomain` (`InitE.sourceInitialState.memaddrs`, preserved by every run) holds
only 8-aligned word cells.  Hence any premise asking `memaddrs` at two consecutive byte addresses (a word-domain
premise `∀ offset < len, memaddrs (key + offset)` with `len ≥ 2`, or an interval-wide `∀ a < bound, D a`) is false at
every actual state.  Byte reads only need the aligned cell (`panByteAlignHOL`), which is what such premises must be
weakened to.
-/
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Compiler.Backend

theorem ordinaryDomain_aligned (a : BitVec 64) (h : ordinaryDomain a) : a.toNat % 8 = 0 := by
  rw [ordinaryDomain, StackRemove.mem_addresses] at h
  obtain ⟨i, hi, rfl⟩ := h
  norm_num [sourceBase, heapEnd, stackStart, ramEnd, ramStart, ramSize, stackSize, globalsWords,
    StackRemove.bytesInWord, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat] at hi ⊢

/-- No two consecutive byte addresses are both actual domain cells. -/
theorem ordinaryDomain_not_consecutive (k : BitVec 64) : ¬ (ordinaryDomain k ∧ ordinaryDomain (k + 1)) := by
  rintro ⟨h0, h1⟩
  have a0 := ordinaryDomain_aligned k h0
  have a1 := ordinaryDomain_aligned (k + 1) h1
  rw [BitVec.toNat_add] at a1
  have : (1 : BitVec 64).toNat = 1 := rfl
  rw [this] at a1
  have hk := k.isLt
  by_cases w : k.toNat + 1 < 2 ^ 64
  · rw [Nat.mod_eq_of_lt w] at a1; omega
  · have : k.toNat + 1 = 2 ^ 64 := by omega
    rw [this, Nat.mod_self] at a1
    omega

/-- The interval-wide domain premise `∀ a < 33806089496, D a` is false for the actual domain. -/
theorem ordinaryDomain_not_all : ¬ (∀ a : BitVec 64, a.toNat < 33806089496 → ordinaryDomain a) := by
  intro h
  have := ordinaryDomain_aligned 1 (h 1 (by decide))
  simp at this

/-- A word-domain premise over the bytes of a key of length `≥ 2` is false for the actual domain. -/
theorem ordinaryDomain_not_keyWords (key : BitVec 64) (len : Nat) (hl : 2 ≤ len) :
    ¬ (∀ offset : Nat, offset < len → ordinaryDomain (key + BitVec.ofNat 64 offset)) := by
  intro h
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0
  exact ordinaryDomain_not_consecutive key ⟨by simpa using h0, h1⟩

#print axioms ordinaryDomain_aligned
#print axioms ordinaryDomain_not_consecutive
#print axioms ordinaryDomain_not_all
#print axioms ordinaryDomain_not_keyWords
end InitECandidate.Runtime
