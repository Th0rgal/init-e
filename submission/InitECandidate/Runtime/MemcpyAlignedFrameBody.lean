import InitECandidate.Runtime.MemcpyAlignedBody
import InitECandidate.Runtime.MemcpyWord32FrameLoop
import InitECandidate.Runtime.MemcpyAlignedFrameSuffix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original aligned copy preserves a watched word outside all writes. -/
theorem evaluate_source_memcpy_aligned_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination source size watched : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (srcLocal : state.locals.lookup (ofString "src") = some (.val (.word source)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (small : destination.toNat + size.toNat ≤ 33806089496)
    (aligned : destination.toNat % 8 = 0) (sourceAligned : source.toNat % 8 = 0) (budget : size.toNat ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (destination + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (destination + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (source + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (source + BitVec.ofNat 64 offset)))
    (wordSeparate : ∀ offset : Nat, offset < size.toNat → watched ≠ destination + BitVec.ofNat 64 offset)
    (byteSeparate : ∀ offset : Nat, offset < size.toNat → watched ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset)) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_memcpy) =
        (some (.returned (.val (.word 0))),post) ∧ post.memory watched = state.memory watched ∧
      state.clock ≤ post.clock + size.toNat ∧ post.clock ≤ state.clock ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let entered := setVarHOLFinite (ofString "i") (.val (.word 0)) state
  have namesDst : ofString "i" ≠ ofString "dst" := by decide
  have namesSrc : ofString "i" ≠ ofString "src" := by decide
  have namesSize : ofString "i" ≠ ofString "n" := by decide
  have dst : entered.locals.lookup (ofString "dst") = some (.val (.word destination)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,namesDst,dstLocal]
  have src : entered.locals.lookup (ofString "src") = some (.val (.word source)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,namesSrc,srcLocal]
  have sizeBinding : entered.locals.lookup (ofString "n") = some (.val (.word size)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,namesSize,sizeLocal]
  have initialIndex : entered.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨wordPost,index,words,indexLocal,inside,remainder,wordCount,reserve,wordClock,
    wordGlobals,wordCode,wordAddresses,wordEndian,wordLocals⟩ :=
    evaluate_memcpy_word32_frame_loop destination source size watched small _ entered 0 dst src sizeBinding initialIndex
      (by simp) rfl (by simpa [entered,setVarHOLFinite] using budget) wordDomain sourceWordDomain wordSeparate
  have srcAfter := (wordLocals (ofString "src") (by decide)).trans src
  have dstAfter := (wordLocals (ofString "dst") (by decide)).trans dst
  have sizeAfter := (wordLocals (ofString "n") (by decide)).trans sizeBinding
  have wordsDomain : ∀ offset : Nat, offset < size.toNat → wordPost.memaddrs (destination + BitVec.ofNat 64 offset) := by
    intro offset bound; rw [wordAddresses]; exact wordDomain offset bound
  have bytesDomain : ∀ offset : Nat, offset < size.toNat → wordPost.memaddrs (panByteAlignHOL (destination + BitVec.ofNat 64 offset)) := by
    intro offset bound; rw [wordAddresses]; exact byteDomain offset bound
  have sourceWordsDomain : ∀ offset : Nat, offset < size.toNat → wordPost.memaddrs (source + BitVec.ofNat 64 offset) := by
    intro offset bound; rw [wordAddresses]; exact sourceWordDomain offset bound
  have sourceBytesDomain : ∀ offset : Nat, offset < size.toNat → wordPost.memaddrs (panByteAlignHOL (source + BitVec.ofNat 64 offset)) := by
    intro offset bound; rw [wordAddresses]; exact sourceByteDomain offset bound
  obtain ⟨tailPost,tail,tailCount,cost,tailClock,tailGlobals,tailCode,tailAddresses,tailEndian⟩ :=
    evaluate_memcpy_aligned_frame_suffix wordPost destination source size index watched small dstAfter srcAfter sizeAfter indexLocal inside
      (by change state.clock + (size.toNat - index.toNat) ≤ wordPost.clock + size.toNat at reserve; omega) wordsDomain bytesDomain sourceWordsDomain sourceBytesDomain wordSeparate byteSeparate
  have choice : evaluateHOLFiniteState entered
      (.ite memcpyAlignmentCondition (.seq memcpyWord32Loop memcpyWord8Loop) .skip) =
        evaluateHOLFiniteState entered (.seq memcpyWord32Loop memcpyWord8Loop) := by
    rw [evaluateHOLFiniteState_ite,eval_memcpy_aligned_condition entered destination source dst src aligned sourceAligned]
    rfl
  have selected : evaluateHOLFiniteState entered memcpyAfterIndex =
      evaluateHOLFiniteState entered (.seq memcpyWord32Loop memcpyAlignedSuffix) := by
    calc
      _ = evaluateHOLFiniteState entered (.seq (.seq memcpyWord32Loop memcpyWord8Loop)
          (.seq memcpyByte8Loop (.seq memcpyByte1Loop (.return (.const 0))))) := by
        unfold memcpyAfterIndex
        rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_seq_line780,choice]
      _ = _ := evaluate_seq_assoc entered _ _ _
  have run := selected.trans (evaluate_seq_none words tail)
  let post := {tailPost with locals := (HolFiniteMapExact.resVarEq tailPost.locals
    (ofString "i",state.locals.lookup (ofString "i")))}
  refine ⟨post,?_,tailCount.trans wordCount,?_,?_,tailGlobals.trans wordGlobals,tailCode.trans wordCode,
    tailAddresses.trans wordAddresses,tailEndian.trans wordEndian⟩
  · rw [source_memcpy_scoped_body,evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact]
    have shapeOk : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) = true := by
      simp [shapeEqHOL,shapeOfHOLExact]
    rw [if_pos shapeOk,run]
  · change state.clock ≤ tailPost.clock + size.toNat
    change state.clock + (size.toNat - index.toNat) ≤ wordPost.clock + size.toNat at reserve
    omega
  · change tailPost.clock ≤ state.clock
    change wordPost.clock ≤ state.clock at wordClock
    omega

#print axioms evaluate_source_memcpy_aligned_frame
end InitECandidate.Runtime
