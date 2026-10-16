import InitECandidate.Runtime.MemeqSelect32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def memeqAlignmentCondition : ExpHOL 64 :=
  .cmp .equal (.op .and [.op .or [.var .local (ofString "a"),.var .local (ofString "b")],.const 7]) (.const 0)

def memeqAfterAligned : ProgHOL 64 :=
  match memeqDecodedBody with | .dec _ _ _ (.seq _ rest) => rest | _ => .skip

theorem source_memeq_scoped_body : sourceFunctionBody Guest.guestFn_memeq =
    .dec (ofString "i") .one (.const 0)
      (.seq (.ite memeqAlignmentCondition memeqAlignedBody .skip) memeqAfterAligned) := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  rfl

theorem eval_memeq_alignment {F : Type} (state : PanSemStateFiniteExact 64 F) (a b : BitVec 64)
    (aLocal : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (bLocal : state.locals.lookup (ofString "b") = some (.val (.word b)))
    (aAligned : a.toNat % 8 = 0) (bAligned : b.toNat % 8 = 0) :
    @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      memeqAlignmentCondition = some (.val (.word (1 : BitVec 64))) := by
  have mask : ∀ value : BitVec 64, value.toNat % 8 = 0 → value &&& 7 = 0 := by
    intro value aligned
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and]
    change value.toNat &&& (2^3 - 1) = 0
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact aligned
  have both : (a ||| b) &&& (7 : BitVec 64) = 0 := by
    rw [BitVec.and_or_distrib_right,mask a aAligned,mask b bAligned]
    rfl
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .and [.op .or [.var .local (ofString "a"),.var .local (ofString "b")],.const 7]) =
        some (.val (.word (0 : BitVec 64))) := by
    simp [evalHOLExact,evalListHOLExact,aLocal,bLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
    change (a ||| (b ||| 0)) &&& ((7 : BitVec 64) &&& BitVec.allOnes 64) = 0
    have bz : b ||| (0 : BitVec 64) = b := by exact BitVec.or_zero
    rw [bz,BitVec.and_allOnes]
    exact both
  unfold memeqAlignmentCondition
  rw [evalHOLExact,loaded]
  rfl

/-- Complete original memeq body for aligned32-byte keys: a Boolean result,
zero clocks, and unchanged memory, globals and execution metadata. -/
theorem evaluate_source_memeq32 {F : Type} (state : PanSemStateFiniteExact 64 F) (a b : BitVec 64)
    (aLocal : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (bLocal : state.locals.lookup (ofString "b") = some (.val (.word b)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word (32 : BitVec 64))))
    (aAligned : a.toNat % 8 = 0) (bAligned : b.toNat % 8 = 0)
    (domain : ∀ offset ∈ ([0,8,16,24] : List Nat),
      state.memaddrs (a + BitVec.ofNat 64 offset) ∧ state.memaddrs (b + BitVec.ofNat 64 offset)) :
    ∃ value : BitVec 64, ∃ post, (value = 0 ∨ value = 1) ∧
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_memeq) = (some (.returned (.val (.word value))),post) ∧
      post.clock = state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let entered := setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state
  have na : ofString "i" ≠ ofString "a" := by decide
  have nb : ofString "i" ≠ ofString "b" := by decide
  have nn : ofString "i" ≠ ofString "n" := by decide
  have a' : entered.locals.lookup (ofString "a") = some (.val (.word a)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,na] using aLocal
  have b' : entered.locals.lookup (ofString "b") = some (.val (.word b)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nb] using bLocal
  have n' : entered.locals.lookup (ofString "n") = some (.val (.word (32 : BitVec 64))) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nn] using sizeLocal
  have aligned := eval_memeq_alignment entered a b a' b' aAligned bAligned
  obtain ⟨value,boolean,run⟩ := evaluate_memeq_aligned32 entered a b a' b' n' domain
  have selected : evaluateHOLFiniteState entered
      (.seq (.ite memeqAlignmentCondition memeqAlignedBody .skip) memeqAfterAligned) =
      (some (.returned (.val (.word value))),emptyLocalsHOLFinite entered) := by
    rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,aligned]
    simp only [show ¬(1 : BitVec 64) = 0 by decide,run]
    rfl
  rw [source_memeq_scoped_body,evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact]
  have shapeOk : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) = true := by
    simp [shapeEqHOL,shapeOfHOLExact]
  rw [if_pos shapeOk,selected]
  exact ⟨value,_,boolean,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms source_memeq_scoped_body
#print axioms eval_memeq_alignment
#print axioms evaluate_source_memeq32
end InitECandidate.Runtime
