import InitECandidate.Runtime.RlpReaderInputWindow
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Equal whole-input byte reads restrict to the remaining input at any
bounded traversal cursor, including modular pointer arithmetic. -/
theorem rlpInput_suffix_reads {F : Type} (first second : PanSemStateFiniteExact 64 F)
    (pointer length cursor : BitVec 64) (bounded : cursor.toNat ≤ length.toNat)
    (reads : ∀ offset : Nat, offset < length.toNat →
      @panMemLoadByteHOL 64 _ first.memory first.memaddrs (fun a => Classical.propDecidable (first.memaddrs a)) first.be (pointer + BitVec.ofNat 64 offset) =
      @panMemLoadByteHOL 64 _ second.memory second.memaddrs (fun a => Classical.propDecidable (second.memaddrs a)) second.be (pointer + BitVec.ofNat 64 offset)) :
    ∀ offset : Nat, offset < (length - cursor).toNat →
      @panMemLoadByteHOL 64 _ first.memory first.memaddrs (fun a => Classical.propDecidable (first.memaddrs a)) first.be ((pointer + cursor) + BitVec.ofNat 64 offset) =
      @panMemLoadByteHOL 64 _ second.memory second.memaddrs (fun a => Classical.propDecidable (second.memaddrs a)) second.be ((pointer + cursor) + BitVec.ofNat 64 offset) := by
  intro offset inside
  have remaining : (length - cursor).toNat = length.toNat - cursor.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr bounded)
  have address : pointer + BitVec.ofNat 64 (cursor.toNat + offset) =
      (pointer + cursor) + BitVec.ofNat 64 offset := by
    simp [BitVec.ofNat_add,BitVec.add_assoc]
  rw [← address]
  exact reads (cursor.toNat + offset) (by omega)

#print axioms rlpInput_suffix_reads
end InitECandidate.Runtime
