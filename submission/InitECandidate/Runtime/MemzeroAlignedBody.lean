import InitECandidate.Runtime.MemzeroWord32Loop
import InitECandidate.Runtime.MemzeroAlignedSuffix
import InitECandidate.Runtime.PanSeqAssoc
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def memzeroAlignmentCondition : ExpHOL 64 :=
  .cmp .equal (.op .and [.var .local (ofString "dst"),.const 7]) (.const 0)

def memzeroAfterIndex : ProgHOL 64 :=
  .seq (.ite memzeroAlignmentCondition (.seq memzeroWord32Loop memzeroWord8Loop) .skip)
    (.seq memzeroByte8Loop (.seq memzeroByte1Loop (.return (.const 0))))

theorem source_memzero_scoped_body : sourceFunctionBody Guest.guestFn_memzero =
    .dec (ofString "i") .one (.const 0) memzeroAfterIndex := by
  rw [source_memzero_body]
  rfl

theorem eval_memzero_aligned_condition {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (aligned : destination.toNat % 8 = 0) :
    @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) memzeroAlignmentCondition =
        some (.val (.word 1)) := by
  have mask : destination &&& (7 : BitVec 64) = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and]
    change destination.toNat &&& (2^3 - 1) = 0
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact aligned
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .and [.var .local (ofString "dst"),.const 7]) = some (.val (.word 0)) := by
    simp [evalHOLExact,evalListHOLExact,dstLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
    exact mask
  unfold memzeroAlignmentCondition
  rw [evalHOLExact,loaded]
  rfl

/-- Complete original aligned memzero body: every requested byte is zero on
return, with at most size source clocks and no change to globals or code. -/
theorem evaluate_source_memzero_aligned {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination size : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (small : destination.toNat + size.toNat ≤ 33806089496)
    (aligned : destination.toNat % 8 = 0) (budget : size.toNat ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (destination + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (destination + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_memzero) =
        (some (.returned (.val (.word 0))),post) ∧ ZeroBytePrefix post destination size.toNat ∧
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
  have initialZero : ZeroBytePrefix entered destination (0 : BitVec 64).toNat := by
    intro offset bound; change offset < 0 at bound; omega
  obtain ⟨wordPost,index,words,indexLocal,inside,remainder,finalAligned,wordZero,reserve,wordClock,
    wordGlobals,wordCode,wordAddresses,wordEndian,wordLocals⟩ :=
    evaluate_memzero_word32_loop destination size small _ entered 0 dst sizeBinding initialIndex
      (by simp) rfl (by simpa [entered,setVarHOLFinite] using budget) (by simpa using aligned) initialZero wordDomain
  have dstAfter := (wordLocals (ofString "dst") (by decide)).trans dst
  have sizeAfter := (wordLocals (ofString "n") (by decide)).trans sizeBinding
  have wordsDomain : ∀ offset : Nat, offset < size.toNat → wordPost.memaddrs (destination + BitVec.ofNat 64 offset) := by
    intro offset bound; rw [wordAddresses]; exact wordDomain offset bound
  have bytesDomain : ∀ offset : Nat, offset < size.toNat → wordPost.memaddrs (panByteAlignHOL (destination + BitVec.ofNat 64 offset)) := by
    intro offset bound; rw [wordAddresses]; exact byteDomain offset bound
  obtain ⟨tailPost,tail,covered,cost,tailClock,tailGlobals,tailCode,tailAddresses,tailEndian⟩ :=
    evaluate_memzero_aligned_suffix wordPost destination size index small dstAfter sizeAfter indexLocal inside
      (by change state.clock + (size.toNat - index.toNat) ≤ wordPost.clock + size.toNat at reserve; omega) finalAligned wordZero wordsDomain bytesDomain
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
  refine ⟨post,?_,covered,?_,?_,tailGlobals.trans wordGlobals,tailCode.trans wordCode,
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

#print axioms source_memzero_scoped_body
#print axioms eval_memzero_aligned_condition
#print axioms evaluate_source_memzero_aligned
end InitECandidate.Runtime
