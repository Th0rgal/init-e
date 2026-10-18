import InitECandidate.Runtime.InputBytesBelowFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Input bytes placed either before the scratch frame or at or above the
scratch ceiling survive any run preserving memory outside [frame, ceiling). -/
theorem input_bytes_of_memory_separated {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length frame : BitVec 64) (ceiling : Nat)
    (separated : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (noWrap : pointer.toNat + length.toNat < 2^64)
    (below : ∀ address : BitVec 64, address.toNat < frame.toNat → post.memory address = state.memory address)
    (above : ∀ address : BitVec 64, ceiling ≤ address.toNat → post.memory address = state.memory address)
    (domain : post.memaddrs = state.memaddrs) (endian : post.be = state.be)
    (offset : Nat) (inside : offset < length.toNat) :
    @panMemLoadByteHOL 64 _ post.memory post.memaddrs
      (fun a => Classical.propDecidable (post.memaddrs a)) post.be (pointer + BitVec.ofNat 64 offset) =
    @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun a => Classical.propDecidable (state.memaddrs a)) state.be (pointer + BitVec.ofNat 64 offset) := by
  rcases separated with before | ⟨ceilingMod, high⟩
  · exact input_bytes_of_memory_below state post pointer length frame before below domain endian offset inside
  have offsetNat : (BitVec.ofNat 64 offset).toNat = offset := by
    change offset % 2^64 = offset
    exact Nat.mod_eq_of_lt (Nat.lt_trans inside length.isLt)
  have addressNat : (pointer + BitVec.ofNat 64 offset).toNat = pointer.toNat + offset := by
    rw [BitVec.toNat_add_of_lt (by rw [offsetNat]; omega),offsetNat]
  have high' : ceiling ≤ (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)).toNat := by
    rw [panByteAlign_toNat64,addressNat]
    omega
  have cell := above _ high'
  by_cases accessible : state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset))
  · have afterAccessible : post.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)) := by rw [domain]; exact accessible
    simp [panMemLoadByteHOL,accessible,afterAccessible,endian,cell]
  · have afterInaccessible : ¬post.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)) := by rw [domain]; exact accessible
    simp [panMemLoadByteHOL,accessible,afterInaccessible]

#print axioms input_bytes_of_memory_separated

end InitECandidate.Runtime
