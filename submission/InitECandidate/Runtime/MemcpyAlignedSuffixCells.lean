import InitECandidate.Runtime.MemcpyAlignedSuffix
import InitECandidate.Runtime.MemcpyWord8LoopCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem evaluate_memcpy_aligned_suffix_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination source size index capacity used : BitVec 64)
    (small : destination.toNat + size.toNat ≤ 33806089496)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (srcLocal : state.locals.lookup (ofString "src") = some (.val (.word source)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (inside : index.toNat ≤ size.toNat) (budget : size.toNat - index.toNat ≤ state.clock)
    (indexAligned : index.toNat % 8 = 0)
    (wordDomain : ∀ offset : Nat, offset < size.toNat → offset % 8 = 0 → state.memaddrs (destination + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (destination + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < size.toNat → offset % 8 = 0 → state.memaddrs (source + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (source + BitVec.ofNat 64 offset)))
    (wordSeparate : ∀ offset : Nat, offset < size.toNat → ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ destination + BitVec.ofNat 64 offset)
    (byteSeparate : ∀ offset : Nat, offset < size.toNat → ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset)) :
    ∃ post, evaluateHOLFiniteState state memcpyAlignedSuffix = (some (.returned (.val (.word 0))),post) ∧
      hashOccupiedCount capacity (hashOccupancyRead post used) = hashOccupiedCount capacity (hashOccupancyRead state used) ∧
      state.clock ≤ post.clock + (size.toNat - index.toNat) ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨wordPost,finalIndex,words,finalLocal,finalInside,finalAligned,remainder,wordCount,reserve,wordClock,
    wordGlobals,wordCode,wordAddresses,wordEndian,wordLocals⟩ :=
    evaluate_memcpy_word8_loop_cells destination source size capacity used small _ state index dstLocal srcLocal sizeLocal indexLocal inside rfl
      budget indexAligned wordDomain sourceWordDomain wordSeparate
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
    evaluate_memcpy_byte1_loop destination source size capacity used small _ wordPost finalIndex dstAfter srcAfter sizeAfter finalLocal
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

#print axioms evaluate_memcpy_aligned_suffix_cells
end InitECandidate.Runtime
