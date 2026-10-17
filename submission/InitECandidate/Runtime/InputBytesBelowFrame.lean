import InitECandidate.Runtime.AllocationSeparation
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Preservation of words below a frame preserves all byte reads from an
input interval ending before that frame, including inaccessible reads. -/
theorem input_bytes_of_memory_below {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length frame : BitVec 64)
    (before : pointer.toNat + length.toNat ≤ frame.toNat)
    (memory : ∀ address : BitVec 64, address.toNat < frame.toNat → post.memory address = state.memory address)
    (domain : post.memaddrs = state.memaddrs) (endian : post.be = state.be)
    (offset : Nat) (inside : offset < length.toNat) :
    @panMemLoadByteHOL 64 _ post.memory post.memaddrs
      (fun a => Classical.propDecidable (post.memaddrs a)) post.be (pointer + BitVec.ofNat 64 offset) =
    @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun a => Classical.propDecidable (state.memaddrs a)) state.be (pointer + BitVec.ofNat 64 offset) := by
  have offsetNat : (BitVec.ofNat 64 offset).toNat = offset := by
    change offset % 2^64 = offset
    exact Nat.mod_eq_of_lt (Nat.lt_trans inside length.isLt)
  have sumBound : pointer.toNat + (BitVec.ofNat 64 offset).toNat < 2^64 := by
    rw [offsetNat]
    have bound := frame.isLt
    omega
  have addressNat : (pointer + BitVec.ofNat 64 offset).toNat = pointer.toNat + offset := by
    rw [BitVec.toNat_add_of_lt sumBound,offsetNat]
  have below : (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)).toNat < frame.toNat := by
    rw [panByteAlign_toNat64,addressNat]
    have rounded := Nat.div_mul_le_self (pointer.toNat + offset) 8
    omega
  have cell := memory _ below
  by_cases accessible : state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset))
  · have afterAccessible : post.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)) := by rw [domain]; exact accessible
    simp [panMemLoadByteHOL,accessible,afterAccessible,endian,cell]
  · have afterInaccessible : ¬post.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)) := by rw [domain]; exact accessible
    simp [panMemLoadByteHOL,accessible,afterInaccessible]

#print axioms input_bytes_of_memory_below
end InitECandidate.Runtime
