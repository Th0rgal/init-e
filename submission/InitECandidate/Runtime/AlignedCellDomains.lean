import InitECandidate.Runtime.MemzeroCoverage
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

theorem panByteAlign_eq_self_aligned (address : BitVec 64)
    (aligned : address.toNat % 8 = 0) : panByteAlignHOL address = address := by
  apply BitVec.eq_of_toNat_eq
  rw [panByteAlign_toNat64]
  omega

/-- An aligned word operation needs only the same cell as a byte operation
at its first byte; no inaccessible unaligned word cells are assumed. -/
theorem aligned_word_domain_of_byte_domain {F : Type}
    (state : PanSemStateFiniteExact 64 F) (destination size : BitVec 64)
    (fits : destination.toNat + size.toNat ≤ 33806089496)
    (domain : ∀ offset : Nat, offset < size.toNat →
      state.memaddrs (panByteAlignHOL (destination + BitVec.ofNat 64 offset)))
    (offset : Nat) (inside : offset < size.toNat)
    (aligned : (destination.toNat + offset) % 8 = 0) :
    state.memaddrs (destination + BitVec.ofNat 64 offset) := by
  have off : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
  have address : (destination + BitVec.ofNat 64 offset).toNat = destination.toNat + offset := by
    rw [BitVec.toNat_add_of_lt (by rw [off]; omega), off]
  have equal := panByteAlign_eq_self_aligned (destination + BitVec.ofNat 64 offset)
    (by rw [address]; exact aligned)
  simpa only [equal] using domain offset inside

#print axioms panByteAlign_eq_self_aligned
#print axioms aligned_word_domain_of_byte_domain

theorem aligned_interval_byte_domains {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination size : BitVec 64) (aligned : destination.toNat % 8 = 0)
    (fits : destination.toNat + size.toNat ≤ 2 ^ 64)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 →
      destination.toNat ≤ address.toNat → address.toNat < destination.toNat + size.toNat →
      state.memaddrs address) :
    ∀ offset : Nat, offset < size.toNat →
      state.memaddrs (panByteAlignHOL (destination + BitVec.ofNat 64 offset)) := by
  intro offset inside
  have off : (BitVec.ofNat 64 offset).toNat = offset :=
    Nat.mod_eq_of_lt (Nat.lt_trans inside size.isLt)
  have interval := hashOccupancy_aligned_interval destination size (BitVec.ofNat 64 offset)
    aligned fits (by rw [off]; exact inside)
  apply arena _ _ interval.1 interval.2
  rw [panByteAlign_toNat64]
  omega

#print axioms aligned_interval_byte_domains

theorem aligned_word_domain_of_byte_domain_modular {F : Type}
    (state : PanSemStateFiniteExact 64 F) (destination size : BitVec 64)
    (baseAligned : destination.toNat % 8 = 0)
    (domain : ∀ offset : Nat, offset < size.toNat →
      state.memaddrs (panByteAlignHOL (destination + BitVec.ofNat 64 offset)))
    (offset : Nat) (inside : offset < size.toNat) (aligned : offset % 8 = 0) :
    state.memaddrs (destination + BitVec.ofNat 64 offset) := by
  have off : (BitVec.ofNat 64 offset).toNat = offset :=
    Nat.mod_eq_of_lt (Nat.lt_trans inside size.isLt)
  have addressAligned : (destination + BitVec.ofNat 64 offset).toNat % 8 = 0 := by
    rw [BitVec.toNat_add, off]
    omega
  simpa only [panByteAlign_eq_self_aligned _ addressAligned] using domain offset inside

#print axioms aligned_word_domain_of_byte_domain_modular
end InitECandidate.Runtime
