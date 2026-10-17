import InitECandidate.Runtime.RlpItemLongStringContract
import InitECandidate.Runtime.RlpItemLongFullBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The full original long-string path returns a positive consumed length
bounded by its supplied input, through both byte and payload-length scopes. -/
theorem rlpItem_long_full_return_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64) (byte : UInt8) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (nonzero : length ≠ 0) (lower : 183 < byte.toNat) (upper : byte.toNat ≤ 191)
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be pointer = some byte)
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item) = (some (.returned value),post)) :
    ∃ payload : BitVec 64, value = rlpItemLongValue pointer ((BitVec.ofNat 64 byte.toNat) - 183) payload ∧
      payload.toNat < length.toNat ∧
      0 < (1 + (((BitVec.ofNat 64 byte.toNat) - 183) + payload)).toNat ∧
      (1 + (((BitVec.ofNat 64 byte.toNat) - 183) + payload)).toNat ≤ length.toNat := by
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
  exact rlpItem_long_after_load_return_contract entered output pointer (BitVec.ofNat 64 byte.toNat) length value
    ((frame _ (by decide)).trans pointerLocal) atByte ((frame _ (by decide)).trans lengthLocal)
    (by change 183 < byte.toNat % 2^64; omega) (by change byte.toNat % 2^64 ≤ 191; omega)
    nonzero code ticks bodyRun

/-- Caller-facing long-string contract: bounded source clock consumption,
terminal outcomes and exact successful item fields with positive progress. -/
theorem evaluate_rlpItem_long_full_contract {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64) (byte : UInt8)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (nonzero : length ≠ 0) (lower : 183 < byte.toNat) (upper : byte.toNat ≤ 191)
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be pointer = some byte)
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item) = (result,post) ∧
      state.clock ≤ post.clock + 11 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧ result ≠ none ∧
      (∀ value, result = some (.returned value) → ∃ payload : BitVec 64,
        value = rlpItemLongValue pointer ((BitVec.ofNat 64 byte.toNat) - 183) payload ∧
        payload.toNat < length.toNat ∧
        0 < (1 + (((BitVec.ofNat 64 byte.toNat) - 183) + payload)).toNat ∧
        (1 + (((BitVec.ofNat 64 byte.toNat) - 183) + payload)).toNat ≤ length.toNat) := by
  obtain ⟨result,post,run,cost,remaining,noTimeout,terminal⟩ := evaluate_rlpItem_long_full_body_bounded
    state pointer length byte pointerLocal lengthLocal nonzero lower upper loaded code ticks
  refine ⟨result,post,run,cost,remaining,noTimeout,terminal,?_⟩
  intro value equal
  exact rlpItem_long_full_return_contract state post pointer length byte value pointerLocal lengthLocal
    nonzero lower upper loaded code ticks (by rw [run]; exact congrArg (fun result => (result,post)) equal)

#print axioms evaluate_rlpItem_long_full_contract
#print axioms rlpItem_long_full_return_contract
end InitECandidate.Runtime
