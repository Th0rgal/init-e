import InitECandidate.Runtime.MemzeroWord8Loop
import InitECandidate.Runtime.MemzeroByte1Loop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def memzeroByte8Body : ProgHOL 64 :=
  match memzeroByte8Loop with | .while _ body => body | _ => .skip

theorem memzeroByte8Loop_shape : memzeroByte8Loop = .while (memzeroBlockCondition 8) memzeroByte8Body := by
  simp only [memzeroByte8Body,memzeroByte8Loop,memzeroDecodedBody,Guest.guestFn_memzero,
    declToHOLStructural,funDeclToHOLStructural,progToHOLStructural,expToHOLStructural,
    expListToHOLStructural,shapeToHOLStructural,List.map_cons,List.map_nil,memzeroBlockCondition]
  rfl

/-- The unrolled byte loop cannot run after the aligned word8 loop leaves a
sub-word remainder. The guard is evaluated in the actual source semantics. -/
theorem evaluate_memzero_byte8_skip {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index size : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (inside : index.toNat ≤ size.toNat) (remainder : size.toNat - index.toNat < 8)
    (small : size.toNat ≤ 33806089496) :
    evaluateHOLFiniteState state memzeroByte8Loop = (none,state) := by
  have advanced : (index + 8).toNat = index.toNat + 8 := by
    rw [BitVec.toNat_add_of_lt (by change index.toNat + 8 < 2^64; omega)]
    rfl
  have flag : Compiler.Encoders.Asm.wordCmpHOL .notLower size (index + 8) = false := by
    change (!decide (size.toNat < (index + 8).toNat)) = false
    have beyond : size.toNat < (index + 8).toNat := by rw [advanced]; omega
    rw [decide_eq_true beyond]
    rfl
  have condition := eval_memzero_block_condition state index size 8 indexLocal sizeLocal
  rw [memzeroByte8Loop_shape,evaluateHOLFiniteState_while_total,evalHOLFinite_eq_toExact,condition,flag]
  simp

def memzeroAlignedSuffix : ProgHOL 64 :=
  .seq memzeroWord8Loop (.seq memzeroByte8Loop (.seq memzeroByte1Loop (.return (.const 0))))

/-- Compose the real word8 loop, skipped unrolled byte loop, and final byte
loop. All requested bytes are zero on return, with a linear source clock bound. -/
theorem evaluate_memzero_aligned_suffix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination size index : BitVec 64)
    (small : destination.toNat + size.toNat ≤ 33806089496)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (inside : index.toNat ≤ size.toNat) (budget : size.toNat - index.toNat ≤ state.clock)
    (aligned : (destination.toNat + index.toNat) % 8 = 0)
    (zero : ZeroBytePrefix state destination index.toNat)
    (wordDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (destination + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (destination + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state memzeroAlignedSuffix = (some (.returned (.val (.word 0))),post) ∧
      ZeroBytePrefix post destination size.toNat ∧
      state.clock ≤ post.clock + (size.toNat - index.toNat) ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨wordPost,finalIndex,words,finalLocal,finalInside,remainder,wordZero,reserve,wordClock,
    wordGlobals,wordCode,wordAddresses,wordEndian,wordLocals⟩ :=
    evaluate_memzero_word8_loop destination size small _ state index dstLocal sizeLocal indexLocal inside rfl
      budget aligned zero wordDomain
  have dstAfter := (wordLocals (ofString "dst") (by decide)).trans dstLocal
  have sizeAfter := (wordLocals (ofString "n") (by decide)).trans sizeLocal
  have skip := evaluate_memzero_byte8_skip wordPost finalIndex size finalLocal sizeAfter finalInside remainder (by omega)
  have tailDomain : ∀ offset : Nat, offset < size.toNat → wordPost.memaddrs
      (panByteAlignHOL (destination + BitVec.ofNat 64 offset)) := by
    intro offset bound; rw [wordAddresses]; exact byteDomain offset bound
  obtain ⟨bytePost,bytes,finalByte,covered,byteClock,byteGlobals,byteCode,byteAddresses,byteEndian,byteLocals⟩ :=
    evaluate_memzero_byte1_loop destination size small _ wordPost finalIndex dstAfter sizeAfter finalLocal
      finalInside rfl (by omega) wordZero tailDomain
  have returned : evaluateHOLFiniteState bytePost (.return (.const 0)) =
      (some (.returned (.val (.word 0))),emptyLocalsHOLFinite bytePost) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  refine ⟨emptyLocalsHOLFinite bytePost,evaluate_seq_none words (evaluate_seq_none skip
    (evaluate_seq_none bytes returned)),covered,?_,?_,byteGlobals.trans wordGlobals,byteCode.trans wordCode,
    byteAddresses.trans wordAddresses,byteEndian.trans wordEndian⟩
  · change state.clock ≤ bytePost.clock + (size.toNat - index.toNat)
    omega
  · change bytePost.clock ≤ state.clock
    omega

#print axioms memzeroByte8Loop_shape
#print axioms evaluate_memzero_byte8_skip
#print axioms evaluate_memzero_aligned_suffix
end InitECandidate.Runtime
