import InitECandidate.Runtime.MemcpyByteStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A word-copy step leaves any distinct watched memory word unchanged. -/
theorem evaluate_memcpy_word8_frame_step {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination source index watched : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (srcLocal : state.locals.lookup (ofString "src") = some (.val (.word source)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (destinationDomain : state.memaddrs (destination + index)) (sourceDomain : state.memaddrs (source + index))
    (separate : watched ≠ destination + index) :
    ∃ post, evaluateHOLFiniteState state memcpyWord8Body = (none,post) ∧ post.clock = state.clock ∧
      post.locals.lookup (ofString "i") = some (.val (.word (index + 8))) ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ name, name ≠ ofString "i" → post.locals.lookup name = state.locals.lookup name) ∧
      post.memory watched = state.memory watched := by
  obtain ⟨value,cell⟩ : ∃ value : BitVec 64, state.memory (source + index) = .word value := by
    cases state.memory (source + index) with | word value => exact ⟨value,rfl⟩
  have run := evaluate_memcpy_word8_body state destination source index value dstLocal srcLocal indexLocal
    destinationDomain sourceDomain cell
  refine ⟨_,run,rfl,?_,rfl,rfl,rfl,rfl,?_,?_⟩
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro name different
    simp [setVarHOLFinite,sourceWriteWord,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  · change (sourceWriteWord state (destination + index) value).memory watched = _
    simp only [sourceWriteWord,if_neg separate]

/-- The byte-store codec updates only the destination's aligned word. -/
theorem evaluate_memcpy_byte1_frame_step {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination source index watched : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (srcLocal : state.locals.lookup (ofString "src") = some (.val (.word source)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (destinationDomain : state.memaddrs (panByteAlignHOL (destination + index)))
    (sourceDomain : state.memaddrs (panByteAlignHOL (source + index)))
    (separate : watched ≠ panByteAlignHOL (destination + index)) :
    ∃ post, evaluateHOLFiniteState state memcpyByte1Body = (none,post) ∧ post.clock = state.clock ∧
      post.locals.lookup (ofString "i") = some (.val (.word (index + 1))) ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ name, name ≠ ofString "i" → post.locals.lookup name = state.locals.lookup name) ∧
      post.memory watched = state.memory watched := by
  obtain ⟨src,srcMemory⟩ : ∃ value : BitVec 64, state.memory (panByteAlignHOL (source + index)) = .word value := by
    cases state.memory (panByteAlignHOL (source + index)) with | word value => exact ⟨value,rfl⟩
  obtain ⟨dst,dstMemory⟩ : ∃ value : BitVec 64, state.memory (panByteAlignHOL (destination + index)) = .word value := by
    cases state.memory (panByteAlignHOL (destination + index)) with | word value => exact ⟨value,rfl⟩
  let byte := panGetByteHOL (source + index) src state.be
  have loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be (source + index) = some byte := by
    simp [panMemLoadByteHOL,srcMemory,sourceDomain,byte]
  have run := evaluate_memcpy_byte1_body state destination source index dst byte dstLocal srcLocal indexLocal
    loaded destinationDomain dstMemory
  refine ⟨_,run,rfl,?_,rfl,rfl,rfl,rfl,?_,?_⟩
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro name different
    simp [setVarHOLFinite,sourceWriteByte,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  · exact sourceWriteByte_memory_other state (destination + index) (BitVec.ofNat 64 byte.toNat) dst watched separate

#print axioms evaluate_memcpy_word8_frame_step
#print axioms evaluate_memcpy_byte1_frame_step
end InitECandidate.Runtime
