import InitECandidate.Runtime.TrieNibbleWordFrame
import InitECandidate.Runtime.AllocationSeparation
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A constructor that preserves memory below its frontier retains every
nibble path allocated wholly before that frontier. -/
theorem TrieNibbleRange.before_allocation {F : Type} {state post : PanSemStateFiniteExact 64 F}
    {nibs length : BitVec 64} (valid : TrieNibbleRange state nibs length) (frontier : BitVec 64)
    (bounded : nibs.toNat + length.toNat ≤ frontier.toNat)
    (memory : ∀ address : BitVec 64, address.toNat < frontier.toNat → post.memory address = state.memory address)
    (domain : post.memaddrs = state.memaddrs) (endian : post.be = state.be) :
    TrieNibbleRange post nibs length := by
  intro offset inside byte loaded
  have small : offset < 2^64 := by have top := length.isLt; omega
  have addressNat : (nibs + BitVec.ofNat 64 offset).toNat = nibs.toNat + offset := by
    rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
    have top := frontier.isLt
    exact Nat.mod_eq_of_lt (by omega)
  have alignedNat := panByteAlign_toNat64 (nibs + BitVec.ofNat 64 offset)
  have down := Nat.div_mul_le_self (nibs + BitVec.ofNat 64 offset).toNat 8
  have below : (panByteAlignHOL (nibs + BitVec.ofNat 64 offset)).toNat < frontier.toNat := by omega
  have sameMemory := memory _ below
  apply valid offset inside byte
  by_cases accessible : state.memaddrs (panByteAlignHOL (nibs + BitVec.ofNat 64 offset))
  · have afterAccessible : post.memaddrs (panByteAlignHOL (nibs + BitVec.ofNat 64 offset)) := by rw [domain]; exact accessible
    simpa [panMemLoadByteHOL,accessible,afterAccessible,sameMemory,endian] using loaded
  · have afterInaccessible : ¬post.memaddrs (panByteAlignHOL (nibs + BitVec.ofNat 64 offset)) := by rw [domain]; exact accessible
    simp [panMemLoadByteHOL,afterInaccessible] at loaded

#print axioms TrieNibbleRange.before_allocation
end InitECandidate.Runtime
