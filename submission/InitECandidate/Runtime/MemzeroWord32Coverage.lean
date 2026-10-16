import InitECandidate.Runtime.MemzeroWordCoverage
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Four aligned word stores extend byte coverage by thirty-two bytes. -/
theorem evaluate_memzero_word32_coverage {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination index : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (domain : state.memaddrs (destination + index))
    (domain8 : state.memaddrs (destination + index + 8))
    (domain16 : state.memaddrs (destination + index + 16))
    (domain24 : state.memaddrs (destination + index + 24))
    (zero : ZeroBytePrefix state destination index.toNat)
    (aligned : (destination.toNat + index.toNat) % 8 = 0)
    (bounded : destination.toNat + index.toNat + 32 ≤ 2 ^ 64) :
    ∃ post, evaluateHOLFiniteState state memzeroWord32Body = (none,post) ∧
      ZeroBytePrefix post destination (index.toNat + 32) ∧ post.clock = state.clock ∧
      post.locals.lookup (ofString "i") = some (.val (.word (index + 32))) ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧
      post.be = state.be ∧ ∀ name, name ≠ ofString "i" → post.locals.lookup name = state.locals.lookup name := by
  let one := sourceWriteWord state (destination + index) 0
  let two := sourceWriteWord one (destination + index + 8) 0
  let three := sourceWriteWord two (destination + index + 16) 0
  let four := sourceWriteWord three (destination + index + 24) 0
  let post := setVarHOLFinite (ofString "i") (.val (.word (index + 32))) four
  have address (offset : Nat) : destination + BitVec.ofNat 64 (index.toNat + offset) =
      destination + index + BitVec.ofNat 64 offset := by
    simp [BitVec.ofNat_add,BitVec.add_assoc]
  have first : ZeroBytePrefix one destination (index.toNat + 8) := by
    have step := ZeroBytePrefix.extend_word state destination index.toNat zero aligned (by omega)
      (by simpa using domain)
    simpa [one] using step
  have second : ZeroBytePrefix two destination (index.toNat + 16) := by
    have step := ZeroBytePrefix.extend_word one destination (index.toNat + 8) first (by omega) (by omega)
      (by rw [address 8]; exact domain8)
    simpa [two,address 8,Nat.add_assoc] using step
  have third : ZeroBytePrefix three destination (index.toNat + 24) := by
    have step := ZeroBytePrefix.extend_word two destination (index.toNat + 16) second (by omega) (by omega)
      (by rw [address 16]; exact domain16)
    simpa [three,address 16,Nat.add_assoc] using step
  have fourth : ZeroBytePrefix four destination (index.toNat + 32) := by
    have step := ZeroBytePrefix.extend_word three destination (index.toNat + 24) third (by omega) (by omega)
      (by rw [address 24]; exact domain24)
    simpa [four,address 24,Nat.add_assoc] using step
  refine ⟨post,evaluate_memzero_word32_body state destination index dstLocal indexLocal domain domain8 domain16 domain24,
    fourth,rfl,?_,rfl,rfl,rfl,rfl,?_⟩
  · simp [post,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro name different
    have backwards := Ne.symm different
    simp [post,four,three,two,one,setVarHOLFinite,sourceWriteWord,HolFiniteMapExact.lookup_update,FUPDATE,backwards]

#print axioms evaluate_memzero_word32_coverage
end InitECandidate.Runtime
