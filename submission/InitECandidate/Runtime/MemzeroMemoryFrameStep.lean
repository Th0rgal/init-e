import InitECandidate.Runtime.MemzeroByteCoverage
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual zero stores preserve a distinct memory word. -/
theorem evaluate_memzero_word8_frame_step {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination index watched : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (destinationDomain : state.memaddrs (destination + index))
    (separate : watched ≠ destination + index) :
    ∃ post, evaluateHOLFiniteState state memzeroWord8Body = (none,post) ∧ post.clock = state.clock ∧
      post.locals.lookup (ofString "i") = some (.val (.word (index + 8))) ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ name, name ≠ ofString "i" → post.locals.lookup name = state.locals.lookup name) ∧
      post.memory watched = state.memory watched := by
  have run := evaluate_memzero_word8_body state destination index dstLocal indexLocal destinationDomain
  refine ⟨_,run,rfl,?_,rfl,rfl,rfl,rfl,?_,?_⟩
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro name different
    simp [setVarHOLFinite,sourceWriteWord,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  · change (sourceWriteWord state (destination + index) 0).memory watched = _
    simp only [sourceWriteWord,if_neg separate]

theorem evaluate_memzero_byte1_frame_step {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination index watched : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (destinationDomain : state.memaddrs (panByteAlignHOL (destination + index)))
    (separate : watched ≠ panByteAlignHOL (destination + index)) :
    ∃ post, evaluateHOLFiniteState state memzeroByte1Body = (none,post) ∧ post.clock = state.clock ∧
      post.locals.lookup (ofString "i") = some (.val (.word (index + 1))) ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ name, name ≠ ofString "i" → post.locals.lookup name = state.locals.lookup name) ∧
      post.memory watched = state.memory watched := by
  obtain ⟨cell,cellMemory⟩ : ∃ value : BitVec 64, state.memory (panByteAlignHOL (destination + index)) = .word value := by
    cases state.memory (panByteAlignHOL (destination + index)) with | word value => exact ⟨value,rfl⟩
  let written := sourceWriteByte state (destination + index) 0 cell
  have store := evaluate_source_storeByte state memzeroBase (.const 0) (destination + index) 0 cell
    (eval_memzeroBase state destination index dstLocal indexLocal) (by rfl) destinationDomain cellMemory
  have run := evaluate_seq_none store (evaluate_memzero_advance written index 1 indexLocal)
  refine ⟨_,run,rfl,?_,rfl,rfl,rfl,rfl,?_,?_⟩
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro name different
    simp [written,setVarHOLFinite,sourceWriteByte,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  · exact sourceWriteByte_memory_other state (destination + index) 0 cell watched separate

#print axioms evaluate_memzero_word8_frame_step
#print axioms evaluate_memzero_byte1_frame_step
end InitECandidate.Runtime
