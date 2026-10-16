import InitECandidate.Runtime.MemcpyAlignedSuffix
import InitECandidate.Runtime.MemcpyWord8FrameLoop
import InitECandidate.Runtime.MemcpyByte1FrameLoop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Compose the real word8 loop, skipped unrolled byte loop, and final byte
loop. A separate occupancy array is preserved, with a linear source clock bound. -/
theorem evaluate_memcpy_aligned_frame_suffix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination source size index watched : BitVec 64)
    (small : destination.toNat + size.toNat ≤ 33806089496)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (srcLocal : state.locals.lookup (ofString "src") = some (.val (.word source)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (inside : index.toNat ≤ size.toNat) (budget : size.toNat - index.toNat ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (destination + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (destination + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (source + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (source + BitVec.ofNat 64 offset)))
    (wordSeparate : ∀ offset : Nat, offset < size.toNat → watched ≠ destination + BitVec.ofNat 64 offset)
    (byteSeparate : ∀ offset : Nat, offset < size.toNat → watched ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset)) :
    ∃ post, evaluateHOLFiniteState state memcpyAlignedSuffix = (some (.returned (.val (.word 0))),post) ∧
      post.memory watched = state.memory watched ∧
      state.clock ≤ post.clock + (size.toNat - index.toNat) ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨wordPost,finalIndex,words,finalLocal,finalInside,remainder,wordCount,reserve,wordClock,
    wordGlobals,wordCode,wordAddresses,wordEndian,wordLocals⟩ :=
    evaluate_memcpy_word8_frame_loop destination source size watched small _ state index dstLocal srcLocal sizeLocal indexLocal inside rfl
      budget wordDomain sourceWordDomain wordSeparate
  have srcAfter := (wordLocals (ofString "src") (by decide)).trans srcLocal
  have dstAfter := (wordLocals (ofString "dst") (by decide)).trans dstLocal
  have sizeAfter := (wordLocals (ofString "n") (by decide)).trans sizeLocal
  have skip := evaluate_memcpy_byte8_skip wordPost finalIndex size finalLocal sizeAfter finalInside remainder (by omega)
  have tailDomain : ∀ offset : Nat, offset < size.toNat → wordPost.memaddrs
      (panByteAlignHOL (destination + BitVec.ofNat 64 offset)) := by
    intro offset bound; rw [wordAddresses]; exact byteDomain offset bound
  have tailSourceDomain : ∀ offset : Nat, offset < size.toNat → wordPost.memaddrs
      (panByteAlignHOL (source + BitVec.ofNat 64 offset)) := by
    intro offset bound; rw [wordAddresses]; exact sourceByteDomain offset bound
  obtain ⟨bytePost,bytes,finalByte,byteCount,byteClock,byteGlobals,byteCode,byteAddresses,byteEndian,byteLocals⟩ :=
    evaluate_memcpy_byte1_frame_loop destination source size watched small _ wordPost finalIndex dstAfter srcAfter sizeAfter finalLocal
      finalInside rfl (by omega) tailDomain tailSourceDomain byteSeparate
  have returned : evaluateHOLFiniteState bytePost (.return (.const 0)) =
      (some (.returned (.val (.word 0))),emptyLocalsHOLFinite bytePost) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  refine ⟨emptyLocalsHOLFinite bytePost,evaluate_seq_none words (evaluate_seq_none skip
    (evaluate_seq_none bytes returned)),byteCount.trans wordCount,?_,?_,byteGlobals.trans wordGlobals,byteCode.trans wordCode,
    byteAddresses.trans wordAddresses,byteEndian.trans wordEndian⟩
  · change state.clock ≤ bytePost.clock + (size.toNat - index.toNat)
    omega
  · change bytePost.clock ≤ state.clock
    omega

#print axioms evaluate_memcpy_aligned_frame_suffix
end InitECandidate.Runtime
