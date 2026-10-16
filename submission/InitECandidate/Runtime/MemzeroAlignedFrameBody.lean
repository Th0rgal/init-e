import InitECandidate.Runtime.MemzeroAlignedBody
import InitECandidate.Runtime.MemzeroWord32FrameLoop
import InitECandidate.Runtime.MemzeroAlignedFrameSuffix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original aligned zeroing body preserves a separate word. -/
theorem evaluate_source_memzero_aligned_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination size watched : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (small : destination.toNat + size.toNat ≤ 33806089496)
    (aligned : destination.toNat % 8 = 0) (budget : size.toNat ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (destination + BitVec.ofNat 64 offset))
    (wordSeparate : ∀ offset : Nat, offset < size.toNat → watched ≠ destination + BitVec.ofNat 64 offset)
    (byteSeparate : ∀ offset : Nat, offset < size.toNat → watched ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (destination + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_memzero) =
        (some (.returned (.val (.word 0))),post) ∧ post.memory watched = state.memory watched ∧
      state.clock ≤ post.clock + size.toNat ∧ post.clock ≤ state.clock ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let entered := setVarHOLFinite (ofString "i") (.val (.word 0)) state
  have namesDst : ofString "i" ≠ ofString "dst" := by decide
  have namesSize : ofString "i" ≠ ofString "n" := by decide
  have dst : entered.locals.lookup (ofString "dst") = some (.val (.word destination)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,namesDst,dstLocal]
  have sizeBinding : entered.locals.lookup (ofString "n") = some (.val (.word size)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,namesSize,sizeLocal]
  have initialIndex : entered.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨wordPost,index,words,indexLocal,inside,remainder,wordFrame,reserve,wordClock,
    wordGlobals,wordCode,wordAddresses,wordEndian,wordLocals⟩ :=
    evaluate_memzero_word32_frame_loop destination size watched small _ entered 0 dst sizeBinding initialIndex
      (by simp) rfl (by simpa [entered,setVarHOLFinite] using budget) wordDomain wordSeparate
  have dstAfter := (wordLocals (ofString "dst") (by decide)).trans dst
  have sizeAfter := (wordLocals (ofString "n") (by decide)).trans sizeBinding
  have wordsDomain : ∀ offset : Nat, offset < size.toNat → wordPost.memaddrs (destination + BitVec.ofNat 64 offset) := by
    intro offset bound; rw [wordAddresses]; exact wordDomain offset bound
  have bytesDomain : ∀ offset : Nat, offset < size.toNat → wordPost.memaddrs (panByteAlignHOL (destination + BitVec.ofNat 64 offset)) := by
    intro offset bound; rw [wordAddresses]; exact byteDomain offset bound
  obtain ⟨tailPost,tail,covered,cost,tailClock,tailGlobals,tailCode,tailAddresses,tailEndian⟩ :=
    evaluate_memzero_aligned_frame_suffix wordPost destination size index watched small dstAfter sizeAfter indexLocal inside
      (by change state.clock + (size.toNat - index.toNat) ≤ wordPost.clock + size.toNat at reserve; omega) wordsDomain wordSeparate byteSeparate bytesDomain
  have choice : evaluateHOLFiniteState entered
      (.ite memzeroAlignmentCondition (.seq memzeroWord32Loop memzeroWord8Loop) .skip) =
        evaluateHOLFiniteState entered (.seq memzeroWord32Loop memzeroWord8Loop) := by
    rw [evaluateHOLFiniteState_ite,eval_memzero_aligned_condition entered destination dst aligned]
    rfl
  have selected : evaluateHOLFiniteState entered memzeroAfterIndex =
      evaluateHOLFiniteState entered (.seq memzeroWord32Loop memzeroAlignedSuffix) := by
    calc
      _ = evaluateHOLFiniteState entered (.seq (.seq memzeroWord32Loop memzeroWord8Loop)
          (.seq memzeroByte8Loop (.seq memzeroByte1Loop (.return (.const 0))))) := by
        unfold memzeroAfterIndex
        rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_seq_line780,choice]
      _ = _ := evaluate_seq_assoc entered _ _ _
  have run := selected.trans (evaluate_seq_none words tail)
  let post := {tailPost with locals := (HolFiniteMapExact.resVarEq tailPost.locals
    (ofString "i",state.locals.lookup (ofString "i")))}
  refine ⟨post,?_,covered.trans wordFrame,?_,?_,tailGlobals.trans wordGlobals,tailCode.trans wordCode,
    tailAddresses.trans wordAddresses,tailEndian.trans wordEndian⟩
  · rw [source_memzero_scoped_body,evaluateHOLFiniteState_dec_total]
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

#print axioms evaluate_source_memzero_aligned_frame
end InitECandidate.Runtime
