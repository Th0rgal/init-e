import InitECandidate.Runtime.MemcpyWord8Loop
import InitECandidate.Runtime.MemcpyByte1Loop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def memcpyByte8Loop : ProgHOL 64 :=
  match memcpyAfterAligned with | .seq loop _ => loop | _ => .skip

def memcpyByte8Body : ProgHOL 64 :=
  match memcpyByte8Loop with | .while _ body => body | _ => .skip

theorem memcpyByte8Loop_shape : memcpyByte8Loop = .while (memzeroBlockCondition 8) memcpyByte8Body := by
  simp only [memcpyByte8Body,memcpyByte8Loop,memcpyAfterAligned,memcpyDecodedBody,Guest.guestFn_memcpy,
    declToHOLStructural,funDeclToHOLStructural,progToHOLStructural,expToHOLStructural,
    expListToHOLStructural,shapeToHOLStructural,List.map_cons,List.map_nil,memzeroBlockCondition]
  rfl

/-- The unrolled byte loop cannot run after the aligned word8 loop leaves a
sub-word remainder. The guard is evaluated in the actual source semantics. -/
theorem evaluate_memcpy_byte8_skip {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index size : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (inside : index.toNat ≤ size.toNat) (remainder : size.toNat - index.toNat < 8)
    (small : size.toNat ≤ 33806089496) :
    evaluateHOLFiniteState state memcpyByte8Loop = (none,state) := by
  have advanced : (index + 8).toNat = index.toNat + 8 := by
    rw [BitVec.toNat_add_of_lt (by change index.toNat + 8 < 2^64; omega)]
    rfl
  have flag : Compiler.Encoders.Asm.wordCmpHOL .notLower size (index + 8) = false := by
    change (!decide (size.toNat < (index + 8).toNat)) = false
    have beyond : size.toNat < (index + 8).toNat := by rw [advanced]; omega
    rw [decide_eq_true beyond]
    rfl
  have condition := eval_memzero_block_condition state index size 8 indexLocal sizeLocal
  rw [memcpyByte8Loop_shape,evaluateHOLFiniteState_while_total,evalHOLFinite_eq_toExact,condition,flag]
  simp

def memcpyAlignedSuffix : ProgHOL 64 :=
  .seq memcpyWord8Loop (.seq memcpyByte8Loop (.seq memcpyByte1Loop (.return (.const 0))))

/-- Compose the real word8 loop, skipped unrolled byte loop, and final byte
loop. A separate occupancy array is preserved, with a linear source clock bound. -/
theorem evaluate_memcpy_aligned_suffix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination source size index capacity used : BitVec 64)
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
    (wordSeparate : ∀ offset : Nat, offset < size.toNat → ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ destination + BitVec.ofNat 64 offset)
    (byteSeparate : ∀ offset : Nat, offset < size.toNat → ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset)) :
    ∃ post, evaluateHOLFiniteState state memcpyAlignedSuffix = (some (.returned (.val (.word 0))),post) ∧
      hashOccupiedCount capacity (hashOccupancyRead post used) = hashOccupiedCount capacity (hashOccupancyRead state used) ∧
      state.clock ≤ post.clock + (size.toNat - index.toNat) ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨wordPost,finalIndex,words,finalLocal,finalInside,remainder,wordCount,reserve,wordClock,
    wordGlobals,wordCode,wordAddresses,wordEndian,wordLocals⟩ :=
    evaluate_memcpy_word8_loop destination source size capacity used small _ state index dstLocal srcLocal sizeLocal indexLocal inside rfl
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

#print axioms memcpyByte8Loop_shape
#print axioms evaluate_memcpy_byte8_skip
#print axioms evaluate_memcpy_aligned_suffix
end InitECandidate.Runtime
