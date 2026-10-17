import InitECandidate.Runtime.HashPartialRead
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def hashWordsTail (offsets : List Nat) (tailOffset : Nat) : ProgHOL 64 :=
  offsets.foldr hashWordThen (hashExpressionTail (hashLoadLE32 tailOffset))

/-- A finite sequence of source word loads and its partial-word tail returns
without consuming clocks or changing nonlocal state. -/
theorem evaluate_hashWordsTail {F : Type} (offsets : List Nat) (tailOffset : Nat)
    (state : PanSemStateFiniteExact 64 F) (pointer hash oldWord : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (wordLocal : state.locals.lookup (ofString "w") = some (.val (.word oldWord)))
    (words : ∀ offset ∈ offsets, state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (bytes : ∀ extra : BitVec 64, extra ∈ [0,1,2,3] →
      state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 tailOffset + extra))) :
    ∃ value post, evaluateHOLFiniteState state (hashWordsTail offsets tailOffset) =
      (some (.returned (.val (.word value))),post) ∧
      post.clock = state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  induction offsets generalizing state hash oldWord with
  | nil =>
    obtain ⟨value,loaded⟩ := eval_hashLoadLE32_readable state pointer tailOffset pointerLocal bytes
    obtain ⟨post,run,frame⟩ := evaluate_hashExpressionTail state (hashLoadLE32 tailOffset)
      hash oldWord value hashLocal wordLocal loaded
    exact ⟨_,post,run,frame⟩
  | cons offset offsets ih =>
    obtain ⟨value,cell⟩ : ∃ value : BitVec 64,
        state.memory (pointer + BitVec.ofNat 64 offset) = .word value := by
      cases state.memory (pointer + BitVec.ofNat 64 offset) with
      | word value => exact ⟨value,rfl⟩
    let middle := setVarHOLFinite (ofString "h") (.val (.word (hash ^^^ value)))
      (setVarHOLFinite (ofString "w") (.val (.word value)) state)
    have hp : ofString "h" ≠ ofString "p" := by decide
    have wp : ofString "w" ≠ ofString "p" := by decide
    have hw : ofString "h" ≠ ofString "w" := by decide
    have p : middle.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
      simp [middle,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hp,wp,pointerLocal]
    have h : middle.locals.lookup (ofString "h") = some (.val (.word (hash ^^^ value))) := by
      simp [middle,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have w : middle.locals.lookup (ofString "w") = some (.val (.word value)) := by
      simp [middle,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hw]
    have remaining : ∀ off ∈ offsets, middle.memaddrs (pointer + BitVec.ofNat 64 off) := by
      intro off member
      exact words off (List.mem_cons_of_mem offset member)
    obtain ⟨result,post,run,frame⟩ := ih middle (hash ^^^ value) value p h w remaining bytes
    have step := evaluate_hashWordThen state pointer hash oldWord value offset
      (hashWordsTail offsets tailOffset) pointerLocal hashLocal wordLocal
      (words offset (by simp)) cell
    refine ⟨result,post,?_,frame⟩
    change evaluateHOLFiniteState state (hashWordThen offset (hashWordsTail offsets tailOffset)) = _
    exact step.trans run

theorem evaluate_hashFast20 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer hash oldWord : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (wordLocal : state.locals.lookup (ofString "w") = some (.val (.word oldWord)))
    (words : ∀ offset ∈ [0,8], state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (bytes : ∀ extra : BitVec 64, extra ∈ [0,1,2,3] →
      state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 16 + extra))) :
    ∃ value post, evaluateHOLFiniteState state hashFast20 =
      (some (.returned (.val (.word value))),post) ∧
      post.clock = state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  rw [source_hash_fast20]
  exact evaluate_hashWordsTail [0,8] 16 state pointer hash oldWord pointerLocal hashLocal wordLocal words bytes

theorem evaluate_hashFast52 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer hash oldWord : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (wordLocal : state.locals.lookup (ofString "w") = some (.val (.word oldWord)))
    (words : ∀ offset ∈ [0,8,16,24,32,40], state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (bytes : ∀ extra : BitVec 64, extra ∈ [0,1,2,3] →
      state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 48 + extra))) :
    ∃ value post, evaluateHOLFiniteState state hashFast52 =
      (some (.returned (.val (.word value))),post) ∧
      post.clock = state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  rw [source_hash_fast52]
  exact evaluate_hashWordsTail [0,8,16,24,32,40] 48 state pointer hash oldWord pointerLocal hashLocal wordLocal words bytes

#print axioms evaluate_hashWordsTail
#print axioms evaluate_hashFast20
#print axioms evaluate_hashFast52
end InitECandidate.Runtime
