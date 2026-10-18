import InitECandidate.Runtime.MemzeroCoverage
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A single readable aligned allocation interval supplies both memzero
address-domain premises, including byte stores rounded down to word cells. -/
theorem memzero_interval_domains {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination size : BitVec 64) (aligned : destination.toNat % 8 = 0)
    (fits : destination.toNat + size.toNat ≤ 2^64)
    (arena : ∀ address : BitVec 64, destination.toNat ≤ address.toNat →
      address.toNat < destination.toNat + size.toNat → state.memaddrs address) :
    (∀ offset : Nat, offset < size.toNat → state.memaddrs (destination + BitVec.ofNat 64 offset)) ∧
    (∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (destination + BitVec.ofNat 64 offset))) := by
  have offsetNat (offset : Nat) (inside : offset < size.toNat) : (BitVec.ofNat 64 offset).toNat = offset :=
    Nat.mod_eq_of_lt (Nat.lt_trans inside size.isLt)
  constructor
  · intro offset inside
    have address : (destination + BitVec.ofNat 64 offset).toNat = destination.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [offsetNat offset inside]; omega),offsetNat offset inside]
    apply arena _ <;> rw [address] <;> omega
  · intro offset inside
    have interval := hashOccupancy_aligned_interval destination size (BitVec.ofNat 64 offset) aligned fits
      (by rw [offsetNat offset inside]; exact inside)
    exact arena _ interval.1 interval.2

#print axioms memzero_interval_domains
end InitECandidate.Runtime
