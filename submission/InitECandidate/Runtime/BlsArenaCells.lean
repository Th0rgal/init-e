import InitECandidate.Runtime.AlignedCellDomains
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

theorem arena_offset_byte_cell {F : Type} (state : PanSemStateFiniteExact 64 F)
    (C base : BitVec 64) (k : Nat)
    (aligned : C.toNat % 8 = 0) (above : C.toNat ≤ base.toNat)
    (room : base.toNat + k < 33806089496)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 →
      C.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address) :
    state.memaddrs (panByteAlignHOL (base + BitVec.ofNat 64 k)) := by
  have sum : (base + BitVec.ofNat 64 k).toNat = base.toNat + k := by
    rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp; omega
  apply arena
  · rw [panByteAlign_toNat64]; omega
  · rw [panByteAlign_toNat64, sum]; omega
  · rw [panByteAlign_toNat64, sum]; omega

theorem arena_offset_word_cell {F : Type} (state : PanSemStateFiniteExact 64 F)
    (C base : BitVec 64) (k : Nat)
    (aligned : C.toNat % 8 = 0) (above : C.toNat ≤ base.toNat)
    (room : base.toNat + k < 33806089496)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 →
      C.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (baseAligned : base.toNat % 8 = 0) (offsetAligned : k % 8 = 0) :
    state.memaddrs (base + BitVec.ofNat 64 k) := by
  have sum : (base + BitVec.ofNat 64 k).toNat = base.toNat + k := by
    rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp; omega
  have self := panByteAlign_eq_self_aligned (base + BitVec.ofNat 64 k)
    (by rw [sum]; omega)
  simpa only [self] using arena_offset_byte_cell state C base k aligned above room arena

#print axioms arena_offset_byte_cell
#print axioms arena_offset_word_cell
end InitECandidate.Runtime
