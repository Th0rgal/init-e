import InitECandidate.Runtime.HashFast32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def hashFast20 : ProgHOL 64 :=
  match hashAlignedBody with | .seq (.ite _ body _) _ => body | _ => .skip

def hashAfter32 : ProgHOL 64 :=
  match hashAlignedBody with | .seq _ (.seq _ rest) => rest | _ => .skip

def hashSizeCondition (size : BitVec 64) : ExpHOL 64 :=
  .cmp .equal (.var .local (ofString "key_len")) (.const size)

theorem source_hash_aligned_prefix : hashAlignedBody =
    .seq (.ite (hashSizeCondition 20) hashFast20 .skip)
      (.seq (.ite (hashSizeCondition 32) hashFast32 .skip) hashAfter32) := by rfl

/-- The actual aligned branch selects and executes its original32-byte hash
fast path, returning without reaching any generic hashing loops. -/
theorem evaluate_hash_aligned32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer hash oldWord : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (wordLocal : state.locals.lookup (ofString "w") = some (.val (.word oldWord)))
    (lengthLocal : state.locals.lookup (ofString "key_len") = some (.val (.word (32 : BitVec 64))))
    (domain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset)) :
    ∃ value : BitVec 64, ∃ post, evaluateHOLFiniteState state hashAlignedBody =
        (some (.returned (.val (.word value))),post) ∧
      post.clock = state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have cell : ∀ offset : Nat, ∃ value : BitVec 64, state.memory (pointer + BitVec.ofNat 64 offset) = .word value := by
    intro offset
    cases state.memory (pointer + BitVec.ofNat 64 offset) with | word value => exact ⟨value,rfl⟩
  obtain ⟨v0,c0⟩ := cell 0
  obtain ⟨v8,c8⟩ := cell 8
  obtain ⟨v16,c16⟩ := cell 16
  obtain ⟨v24,c24⟩ := cell 24
  obtain ⟨post,fast,ticks,memory,globals,code,addresses,endian⟩ := evaluate_hashFast32 state pointer hash oldWord
    v0 v8 v16 v24 pointerLocal hashLocal wordLocal (domain 0 (by simp)) c0 (domain 8 (by simp)) c8
    (domain 16 (by simp)) c16 (domain 24 (by simp)) c24
  have no20 : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (hashSizeCondition 20) =
        some (.val (.word (0 : BitVec 64))) := by
    simp [hashSizeCondition,evalHOLExact,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL]
  have yes32 : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (hashSizeCondition 32) =
        some (.val (.word (1 : BitVec 64))) := by
    simp [hashSizeCondition,evalHOLExact,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL]
  refine ⟨hashFinishValue ((((hash ^^^ v0) ^^^ v8) ^^^ v16) ^^^ v24),post,?_,ticks,memory,globals,code,addresses,endian⟩
  rw [source_hash_aligned_prefix,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,no20]
  simp only [if_pos,evaluateHOLFiniteState_skip]
  rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,yes32]
  simp only [show ¬(1 : BitVec 64) = 0 by decide,fast]
  rfl

#print axioms source_hash_aligned_prefix
#print axioms evaluate_hash_aligned32
end InitECandidate.Runtime
