import InitECandidate.Runtime.RlpHeaderShortListDispatch
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_rlpHeader_body : sourceFunctionBody Guest.guestFn_rlp_item_header =
    .seq (.ite (.cmp .equal (.var .local (ofString "len")) (.const 0))
      (.call (some (none,none)) (ofString "rlp_fail") [.const 1]) .skip)
      (.dec (ofString "b") .one (.loadByte (.var .local (ofString "p"))) rlpHeaderAfterByte) := by
  simp only [rlpHeaderAfterByte,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Full original short-list header execution, from the nonempty check and actual
byte load through every validation outcome and restoration of the byte scope. -/
theorem evaluate_rlpHeader_short_list_full_contract {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64) (byte : UInt8)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (nonzero : length ≠ 0) (lower : 192 ≤ byte.toNat) (upper : byte.toNat ≤ 247)
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be pointer = some byte)
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item_header) = (result,post) ∧
      state.clock ≤ post.clock + 1 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧ result ≠ none ∧
      (∀ value, result = some (.returned value) →
        value = rlpHeaderShortListValue ((BitVec.ofNat 64 byte.toNat) - 192) ∧
        ((BitVec.ofNat 64 byte.toNat) - 192).toNat < length.toNat ∧
        0 < (1 + ((BitVec.ofNat 64 byte.toNat) - 192)).toNat ∧
        (1 + ((BitVec.ofNat 64 byte.toNat) - 192)).toNat ≤ length.toNat) ∧
      post.memory = state.memory ∧ post.globals = state.globals := by
  let entered := setVarHOLFinite (ofString "b") (.val (.word (BitVec.ofNat 64 byte.toNat))) state
  have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "b" ≠ ofString "p" by decide] using pointerLocal
  have atByte : entered.locals.lookup (ofString "b") = some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atTotal : entered.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "b" ≠ ofString "len" by decide] using lengthLocal
  have low : 192 ≤ (BitVec.ofNat 64 byte.toNat).toNat := by change 192 ≤ byte.toNat % 2^64; omega
  have high : (BitVec.ofNat 64 byte.toNat).toNat ≤ 247 := by change byte.toNat % 2^64 ≤ 247; omega
  obtain ⟨result,post,selected,cost,remaining,noTimeout,terminal,returned,memory,globals⟩ :=
    evaluate_rlpHeader_short_list_contract entered (BitVec.ofNat 64 byte.toNat) length atByte atTotal
      low high nonzero code ticks
  have run : evaluateHOLFiniteState entered rlpHeaderAfterByte = (result,post) := by
    rw [evaluate_rlpHeader_short_list_after_load entered (BitVec.ofNat 64 byte.toNat) length atByte atTotal
      low high nonzero code ticks,selected]
  have check : evaluateHOLFiniteState state
      (.ite (.cmp .equal (.var .local (ofString "len")) (.const 0))
        (.call (some (none,none)) (ofString "rlp_fail") [.const 1]) .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    have notZero : length ≠ BitVec.ofNat 64 0 := nonzero
    simp [evalHOLExact,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL,notZero,evaluateHOLFiniteState_skip]
  let final := {post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "b",state.locals.lookup (ofString "b"))}
  refine ⟨result,final,?_,cost,remaining,noTimeout,terminal,returned,memory,globals⟩
  rw [source_rlpHeader_body,evaluateHOLFiniteState_seq_line780,check]
  dsimp only
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,pointerLocal,loaded,Option.map_some,shapeOfHOLExact,shapeEqHOL,if_true]
  change (let result := evaluateHOLFiniteState entered rlpHeaderAfterByte; _) = _
  rw [run]

#print axioms evaluate_rlpHeader_short_list_full_contract
end InitECandidate.Runtime
