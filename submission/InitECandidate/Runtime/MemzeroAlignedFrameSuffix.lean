import InitECandidate.Runtime.MemzeroAlignedSuffix
import InitECandidate.Runtime.MemzeroWord8FrameLoop
import InitECandidate.Runtime.MemzeroByte1FrameLoop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original zeroing tail preserves any word outside its store cells. -/
theorem evaluate_memzero_aligned_frame_suffix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination size index watched : BitVec 64)
    (small : destination.toNat + size.toNat ≤ 33806089496)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (inside : index.toNat ≤ size.toNat) (budget : size.toNat - index.toNat ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (destination + BitVec.ofNat 64 offset))
    (wordSeparate : ∀ offset : Nat, offset < size.toNat → watched ≠ destination + BitVec.ofNat 64 offset)
    (byteSeparate : ∀ offset : Nat, offset < size.toNat → watched ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (destination + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state memzeroAlignedSuffix = (some (.returned (.val (.word 0))),post) ∧
      post.memory watched = state.memory watched ∧
      state.clock ≤ post.clock + (size.toNat - index.toNat) ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨wordPost,finalIndex,words,finalLocal,finalInside,remainder,wordFrame,reserve,wordClock,
    wordGlobals,wordCode,wordAddresses,wordEndian,wordLocals⟩ :=
    evaluate_memzero_word8_frame_loop destination size watched small _ state index dstLocal sizeLocal indexLocal inside rfl
      budget wordDomain wordSeparate
  have dstAfter := (wordLocals (ofString "dst") (by decide)).trans dstLocal
  have sizeAfter := (wordLocals (ofString "n") (by decide)).trans sizeLocal
  have skip := evaluate_memzero_byte8_skip wordPost finalIndex size finalLocal sizeAfter finalInside remainder (by omega)
  have tailDomain : ∀ offset : Nat, offset < size.toNat → wordPost.memaddrs
      (panByteAlignHOL (destination + BitVec.ofNat 64 offset)) := by
    intro offset bound; rw [wordAddresses]; exact byteDomain offset bound
  obtain ⟨bytePost,bytes,finalByte,covered,byteClock,byteGlobals,byteCode,byteAddresses,byteEndian,byteLocals⟩ :=
    evaluate_memzero_byte1_frame_loop destination size watched small _ wordPost finalIndex dstAfter sizeAfter finalLocal
      finalInside rfl (by omega) tailDomain byteSeparate
  have returned : evaluateHOLFiniteState bytePost (.return (.const 0)) =
      (some (.returned (.val (.word 0))),emptyLocalsHOLFinite bytePost) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  refine ⟨emptyLocalsHOLFinite bytePost,evaluate_seq_none words (evaluate_seq_none skip
    (evaluate_seq_none bytes returned)),covered.trans wordFrame,?_,?_,byteGlobals.trans wordGlobals,byteCode.trans wordCode,
    byteAddresses.trans wordAddresses,byteEndian.trans wordEndian⟩
  · change state.clock ≤ bytePost.clock + (size.toNat - index.toNat)
    omega
  · change bytePost.clock ≤ state.clock
    omega

#print axioms evaluate_memzero_aligned_frame_suffix
end InitECandidate.Runtime
