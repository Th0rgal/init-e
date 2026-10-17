import InitECandidate.Runtime.RlpItemShortFullBody
import InitECandidate.Runtime.RlpItemShortScopeProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The full original short-string path returns a positive consumed length
bounded by its supplied input, through both byte and payload-length scopes. -/
theorem rlpItem_short_full_return_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64) (byte : UInt8) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (nonzero : length ≠ 0) (lower : 128 ≤ byte.toNat) (upper : byte.toNat ≤ 183)
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be pointer = some byte)
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item) = (some (.returned value),post)) :
    ((BitVec.ofNat 64 byte.toNat) - 128).toNat < length.toNat ∧
      0 < (1 + ((BitVec.ofNat 64 byte.toNat) - 128)).toNat ∧
      (1 + ((BitVec.ofNat 64 byte.toNat) - 128)).toNat ≤ length.toNat := by
  have check : evaluateHOLFiniteState state
      (.ite (.cmp .equal (.var .local (ofString "len")) (.const 0))
        (.call (some (none,none)) (ofString "rlp_fail") [.const 1]) .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    have notZero : length ≠ BitVec.ofNat 64 0 := nonzero
    simp [evalHOLExact,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL,notZero,evaluateHOLFiniteState_skip]
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.loadByte (.var .local (ofString "p"))) = some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
    simp [evalHOLExact,pointerLocal,loaded]
  rw [source_rlpItem_body,evaluateHOLFiniteState_seq_line780,check] at run
  obtain ⟨output,bodyRun,_⟩ := evaluate_dec_word_result_scope state post (ofString "b")
    (.loadByte (.var .local (ofString "p"))) (BitVec.ofNat 64 byte.toNat) rlpItemAfterByte
    (some (.returned value)) initializer run
  let entered := setVarHOLFinite (ofString "b") (.val (.word (BitVec.ofNat 64 byte.toNat))) state
  have frame : ∀ name, name ≠ ofString "b" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have atByte : entered.locals.lookup (ofString "b") = some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  exact rlpItem_short_after_load_return_progress entered output pointer (BitVec.ofNat 64 byte.toNat) length value
    ((frame _ (by decide)).trans pointerLocal) atByte ((frame _ (by decide)).trans lengthLocal)
    (by change 128 ≤ byte.toNat % 2^64; omega) (by change byte.toNat % 2^64 ≤ 183; omega)
    nonzero code ticks bodyRun

/-- A caller-facing full-body short-string contract combining runtime,
returned-item shape, positive progress, payload bounds and read-only behavior. -/
theorem evaluate_rlpItem_short_full_contract {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64) (byte : UInt8)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (nonzero : length ≠ 0) (lower : 128 ≤ byte.toNat) (upper : byte.toNat ≤ 183)
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be pointer = some byte)
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item) = (result,post) ∧
      state.clock ≤ post.clock + 1 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧ result ≠ none ∧
      (∀ value, result = some (.returned value) → ∃ payload consumed : BitVec 64,
        value = .rStruct [.val (.word (0 : BitVec 64)),.val (.word (pointer + 1)),.val (.word payload),.val (.word consumed)] ∧
        payload.toNat < length.toNat ∧ 0 < consumed.toNat ∧ consumed.toNat ≤ length.toNat) ∧
      post.memory = state.memory ∧ post.globals = state.globals := by
  obtain ⟨result,post,run,cost,remaining,noTimeout,terminal,returned,memory,globals⟩ :=
    evaluate_rlpItem_short_full_body state pointer length byte pointerLocal lengthLocal nonzero lower upper loaded code ticks
  refine ⟨result,post,run,cost,remaining,noTimeout,terminal,?_,memory,globals⟩
  intro value equal
  have progress := rlpItem_short_full_return_progress state post pointer length byte value pointerLocal lengthLocal
    nonzero lower upper loaded code ticks (by rw [run]; exact congrArg (fun result => (result,post)) equal)
  exact ⟨(BitVec.ofNat 64 byte.toNat) - 128,1 + ((BitVec.ofNat 64 byte.toNat) - 128),returned value equal,progress⟩

#print axioms rlpItem_short_full_return_progress
#print axioms evaluate_rlpItem_short_full_contract
end InitECandidate.Runtime
