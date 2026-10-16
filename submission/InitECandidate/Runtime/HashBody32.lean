import InitECandidate.Runtime.HashSelect32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def hashAlignmentCondition : ExpHOL 64 :=
  .cmp .equal (.op .and [.var .local (ofString "p"),.const 7]) (.const 0)
def hashUnalignedBody : ProgHOL 64 :=
  match hashDecodedBody with | .dec _ _ _ (.dec _ _ _ (.seq (.ite _ _ body) _)) => body | _ => .skip
def hashAfterAlignment : ProgHOL 64 :=
  match hashDecodedBody with | .dec _ _ _ (.dec _ _ _ (.seq _ rest)) => rest | _ => .skip

theorem source_hash_scoped_body : sourceFunctionBody Guest.guestFn_htab_hash =
    .dec (ofString "h") .one (.const 14695981039346656037)
      (.dec (ofString "w") .one (.const 0)
        (.seq (.ite hashAlignmentCondition hashAlignedBody hashUnalignedBody) hashAfterAlignment)) := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  rfl

theorem eval_hash_alignment {F : Type} (state : PanSemStateFiniteExact 64 F) (pointer : BitVec 64)
    (binding : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (aligned : pointer.toNat % 8 = 0) :
    @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      hashAlignmentCondition = some (.val (.word (1 : BitVec 64))) := by
  have mask : pointer &&& (7 : BitVec 64) = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and]
    change pointer.toNat &&& (2^3 - 1) = 0
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact aligned
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .and [.var .local (ofString "p"),.const 7]) = some (.val (.word (0 : BitVec 64))) := by
    simp [evalHOLExact,evalListHOLExact,binding,wordOpHOL,wordOp,valueIsWord,valueWord]
    exact mask
  unfold hashAlignmentCondition
  rw [evalHOLExact,loaded]
  rfl

/-- Complete original htab_hash body for an aligned32-byte key, including
its seeded hash local and temporary word scope. All nonlocal state is preserved. -/
theorem evaluate_source_hash32 {F : Type} (state : PanSemStateFiniteExact 64 F) (pointer : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "key_len") = some (.val (.word (32 : BitVec 64))))
    (aligned : pointer.toNat % 8 = 0)
    (domain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset)) :
    ∃ value : BitVec 64, ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_hash) =
        (some (.returned (.val (.word value))),post) ∧
      post.clock = state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let seeded := setVarHOLFinite (ofString "h") (.val (.word (14695981039346656037 : BitVec 64))) state
  let entered := setVarHOLFinite (ofString "w") (.val (.word (0 : BitVec 64))) seeded
  have hp : ofString "h" ≠ ofString "p" := by decide
  have wp : ofString "w" ≠ ofString "p" := by decide
  have hn : ofString "h" ≠ ofString "key_len" := by decide
  have wn : ofString "w" ≠ ofString "key_len" := by decide
  have wh : ofString "w" ≠ ofString "h" := by decide
  have p : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [entered,seeded,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hp,wp] using pointerLocal
  have n : entered.locals.lookup (ofString "key_len") = some (.val (.word (32 : BitVec 64))) := by
    simpa [entered,seeded,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hn,wn] using lengthLocal
  have h : entered.locals.lookup (ofString "h") = some (.val (.word (14695981039346656037 : BitVec 64))) := by
    simp [entered,seeded,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,wh]
  have w : entered.locals.lookup (ofString "w") = some (.val (.word (0 : BitVec 64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨value,post,run,ticks,memory,globals,code,addresses,endian⟩ :=
    evaluate_hash_aligned32 entered pointer 14695981039346656037 0 p h w n domain
  have condition := eval_hash_alignment entered pointer p aligned
  have selected : evaluateHOLFiniteState entered
      (.seq (.ite hashAlignmentCondition hashAlignedBody hashUnalignedBody) hashAfterAlignment) =
      (some (.returned (.val (.word value))),post) := by
    rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition]
    simp only [show ¬(1 : BitVec 64) = 0 by decide,run]
    rfl
  rw [source_hash_scoped_body,evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact]
  have seedShape : shapeEqHOL .one (shapeOfHOLExact (.val (.word (14695981039346656037 : BitVec 64)))) = true := by
    simp [shapeOfHOLExact,shapeEqHOL]
  rw [if_pos seedShape,evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact]
  have wordShape : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) = true := by
    simp [shapeOfHOLExact,shapeEqHOL]
  rw [if_pos wordShape,selected]
  exact ⟨value,_,rfl,ticks,memory,globals,code,addresses,endian⟩

#print axioms source_hash_scoped_body
#print axioms eval_hash_alignment
#print axioms evaluate_source_hash32
end InitECandidate.Runtime
