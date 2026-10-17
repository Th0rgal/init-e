import InitECandidate.Runtime.HashFastWidths
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_hash_after32 : hashAfter32 =
    .ite (hashSizeCondition 52) hashFast52 .skip := by rfl

theorem evaluate_hash_aligned20 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer hash oldWord : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (wordLocal : state.locals.lookup (ofString "w") = some (.val (.word oldWord)))
    (lengthLocal : state.locals.lookup (ofString "key_len") = some (.val (.word (20 : BitVec 64))))
    (words : ∀ offset ∈ ([0,8] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (bytes : ∀ extra : BitVec 64, extra ∈ [0,1,2,3] →
      state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 16 + extra))) :
    ∃ value post, evaluateHOLFiniteState state hashAlignedBody =
      (some (.returned (.val (.word value))),post) ∧
      post.clock = state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨value,post,fast,frame⟩ := evaluate_hashFast20 state pointer hash oldWord
    pointerLocal hashLocal wordLocal words bytes
  have test20 : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (hashSizeCondition 20) =
        some (.val (.word (1 : BitVec 64))) := by
    simp [hashSizeCondition,evalHOLExact,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL]
  refine ⟨value,post,?_,frame⟩
  rw [source_hash_aligned_prefix,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,test20]
  simp only [show ¬(1 : BitVec 64) = 0 by decide,fast]
  rfl

theorem evaluate_hash_aligned52 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer hash oldWord : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (wordLocal : state.locals.lookup (ofString "w") = some (.val (.word oldWord)))
    (lengthLocal : state.locals.lookup (ofString "key_len") = some (.val (.word (52 : BitVec 64))))
    (words : ∀ offset ∈ ([0,8,16,24,32,40] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (bytes : ∀ extra : BitVec 64, extra ∈ [0,1,2,3] →
      state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 48 + extra))) :
    ∃ value post, evaluateHOLFiniteState state hashAlignedBody =
      (some (.returned (.val (.word value))),post) ∧
      post.clock = state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨value,post,fast,frame⟩ := evaluate_hashFast52 state pointer hash oldWord
    pointerLocal hashLocal wordLocal words bytes
  have test20 : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (hashSizeCondition 20) =
        some (.val (.word (0 : BitVec 64))) := by
    simp [hashSizeCondition,evalHOLExact,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL]
  have test32 : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (hashSizeCondition 32) =
        some (.val (.word (0 : BitVec 64))) := by
    simp [hashSizeCondition,evalHOLExact,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL]
  have test52 : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (hashSizeCondition 52) =
        some (.val (.word (1 : BitVec 64))) := by
    simp [hashSizeCondition,evalHOLExact,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL]
  refine ⟨value,post,?_,frame⟩
  rw [source_hash_aligned_prefix,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,test20]
  simp only [if_pos,evaluateHOLFiniteState_skip]
  rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,test32]
  simp only [if_pos,evaluateHOLFiniteState_skip]
  rw [source_hash_after32,evaluateHOLFiniteState_ite,test52]
  simp only [show ¬(1 : BitVec 64) = 0 by decide]
  exact fast

#print axioms evaluate_hash_aligned20
#print axioms evaluate_hash_aligned52
end InitECandidate.Runtime
