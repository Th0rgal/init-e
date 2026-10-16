import InitECandidate.Runtime.MemzeroWordCoverage
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The real byte tail body advances exactly one byte and preserves its
completed prefix, including neighboring bytes in the changed aligned word. -/
theorem evaluate_memzero_byte1_coverage {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination index cell : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (domain : state.memaddrs (panByteAlignHOL (destination + index)))
    (memory : state.memory (panByteAlignHOL (destination + index)) = .word cell)
    (zero : ZeroBytePrefix state destination index.toNat)
    (bounded : destination.toNat + index.toNat + 1 ≤ 2 ^ 64) :
    ∃ post, evaluateHOLFiniteState state memzeroByte1Body = (none,post) ∧
      ZeroBytePrefix post destination (index.toNat + 1) ∧ post.clock = state.clock ∧
      post.locals.lookup (ofString "i") = some (.val (.word (index + 1))) ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧
      post.be = state.be ∧ ∀ name, name ≠ ofString "i" → post.locals.lookup name = state.locals.lookup name := by
  let written := sourceWriteByte state (destination + index) 0 cell
  let post := setVarHOLFinite (ofString "i") (.val (.word (index + 1))) written
  have store := evaluate_source_storeByte state memzeroBase (.const 0) (destination + index) 0 cell
    (eval_memzeroBase state destination index dstLocal indexLocal) (by rfl) domain memory
  have body := evaluate_seq_none store (evaluate_memzero_advance written index 1 indexLocal)
  have covered := ZeroBytePrefix.extend_byte state destination cell index.toNat zero bounded
    (by simpa using domain) (by simpa using memory)
  refine ⟨post,body,?_,rfl,?_,rfl,rfl,rfl,rfl,?_⟩
  · change ZeroBytePrefix written destination (index.toNat + 1)
    simpa [written] using covered
  · simp [post,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro name different
    have backwards := Ne.symm different
    simp [post,written,setVarHOLFinite,sourceWriteByte,HolFiniteMapExact.lookup_update,FUPDATE,backwards]

#print axioms evaluate_memzero_byte1_coverage
end InitECandidate.Runtime
