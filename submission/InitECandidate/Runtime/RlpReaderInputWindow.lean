import InitECandidate.Runtime.RlpReadLengthBodyRangeAgreement
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A header's available length bytes are a subrange of the supplied input. -/
theorem rlpReader_input_window {F : Type} (first second : PanSemStateFiniteExact 64 F)
    (pointer total count : BitVec 64) (fits : 1 + count.toNat ≤ total.toNat)
    (reads : ∀ offset : Nat, offset < total.toNat →
      @panMemLoadByteHOL 64 _ first.memory first.memaddrs (fun a => Classical.propDecidable (first.memaddrs a)) first.be (pointer + BitVec.ofNat 64 offset) =
      @panMemLoadByteHOL 64 _ second.memory second.memaddrs (fun a => Classical.propDecidable (second.memaddrs a)) second.be (pointer + BitVec.ofNat 64 offset)) :
    ∀ offset : BitVec 64, offset.toNat < count.toNat →
      @panMemLoadByteHOL 64 _ first.memory first.memaddrs (fun a => Classical.propDecidable (first.memaddrs a)) first.be ((pointer + 1) + offset) =
      @panMemLoadByteHOL 64 _ second.memory second.memaddrs (fun a => Classical.propDecidable (second.memaddrs a)) second.be ((pointer + 1) + offset) := by
  intro offset inside
  have equal : pointer + BitVec.ofNat 64 (1 + offset.toNat) = (pointer + 1) + offset := by
    simp [BitVec.ofNat_add,BitVec.add_assoc]
  rw [← equal]
  exact reads (1 + offset.toNat) (by omega)

#print axioms rlpReader_input_window
end InitECandidate.Runtime
