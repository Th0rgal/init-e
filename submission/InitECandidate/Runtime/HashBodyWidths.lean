import InitECandidate.Runtime.HashBody32
import InitECandidate.Runtime.HashSelectWidths
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

theorem evaluate_source_hash20 {F : Type} (state : PanSemStateFiniteExact 64 F) (pointer : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "key_len") = some (.val (.word (20 : BitVec 64))))
    (aligned : pointer.toNat % 8 = 0)
    (domain : ∀ offset ∈ ([0,8] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset)) 
    (bytes : ∀ extra : BitVec 64, extra ∈ [0,1,2,3] →
      state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 16 + extra))) :
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
  have n : entered.locals.lookup (ofString "key_len") = some (.val (.word (20 : BitVec 64))) := by
    simpa [entered,seeded,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hn,wn] using lengthLocal
  have h : entered.locals.lookup (ofString "h") = some (.val (.word (14695981039346656037 : BitVec 64))) := by
    simp [entered,seeded,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,wh]
  have w : entered.locals.lookup (ofString "w") = some (.val (.word (0 : BitVec 64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨value,post,run,ticks,memory,globals,code,addresses,endian⟩ :=
    evaluate_hash_aligned20 entered pointer 14695981039346656037 0 p h w n domain bytes
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


theorem evaluate_source_hash52 {F : Type} (state : PanSemStateFiniteExact 64 F) (pointer : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "key_len") = some (.val (.word (52 : BitVec 64))))
    (aligned : pointer.toNat % 8 = 0)
    (domain : ∀ offset ∈ ([0,8,16,24,32,40] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset)) 
    (bytes : ∀ extra : BitVec 64, extra ∈ [0,1,2,3] →
      state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 48 + extra))) :
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
  have n : entered.locals.lookup (ofString "key_len") = some (.val (.word (52 : BitVec 64))) := by
    simpa [entered,seeded,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hn,wn] using lengthLocal
  have h : entered.locals.lookup (ofString "h") = some (.val (.word (14695981039346656037 : BitVec 64))) := by
    simp [entered,seeded,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,wh]
  have w : entered.locals.lookup (ofString "w") = some (.val (.word (0 : BitVec 64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨value,post,run,ticks,memory,globals,code,addresses,endian⟩ :=
    evaluate_hash_aligned52 entered pointer 14695981039346656037 0 p h w n domain bytes
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


#print axioms evaluate_source_hash20
#print axioms evaluate_source_hash52
end InitECandidate.Runtime
