import InitECandidate.Runtime.OriginalRlpDecodeFullyCode
import InitECandidate.Runtime.RlpDecodeFullyBodyRange
import InitECandidate.Runtime.PanDecCallNormalReturnProperty
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal completion of the original full-decoder declaration binds the
proved item shape and executes its continuation with caller locals restored. -/
theorem evaluate_rlpDecodeFully_declaration_range {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (pointer length : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (code : state.code = originalRuntimeCode) (ticks : 13 ≤ state.clock)
    (inputRange : pointer.toNat + length.toNat < 2^64) (inputBound : length.toNat + 9 < 2^64)
    (run : evaluateHOLFiniteState state ( .decCall name (.comb [.one,.one,.one,.one]) (ofString "rlp_decode_fully") arguments continuation) = (none,post)) :
    ∃ (kind payloadPointer payload : BitVec 64) (ready output : PanSemStateFiniteExact 64 F),
      (kind = 0 ∨ kind = 1) ∧ payload.toNat ≤ length.toNat ∧ 0 < length.toNat ∧
      payloadPointer.toNat + payload.toNat ≤ pointer.toNat + length.toNat ∧
      payloadPointer.toNat + payload.toNat < 2^64 ∧ pointer.toNat ≤ payloadPointer.toNat ∧ ready.locals = state.locals ∧
      evaluateHOLFiniteState (setVarHOLFinite name
        (.rStruct [.val (.word kind),.val (.word payloadPointer),.val (.word payload),.val (.word length)]) ready)
        continuation = (none,output) ∧
      post = {output with locals := HolFiniteMapExact.resVarEq output.locals (name,state.locals.lookup name)} := by
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have pointerLocal : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have lengthLocal : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have installed : state.code.lookup (ofString "rlp_decode_fully") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_decode_fully,.comb [.one,.one,.one,.one]) := by
    rw [code]; exact originalRuntimeCode_rlpDecodeFully_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_decode_fully") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_rlp_decode_fully) (.comb [.one,.one,.one,.one]) pointer length (by decide) installed
  let property := fun value : ValueHOL 64 => ∃ kind payloadPointer payload : BitVec 64,
    value = .rStruct [.val (.word kind),.val (.word payloadPointer),.val (.word payload),.val (.word length)] ∧
      (kind = 0 ∨ kind = 1) ∧ payload.toNat ≤ length.toNat ∧ 0 < length.toNat ∧
      payloadPointer.toNat + payload.toNat ≤ pointer.toNat + length.toNat ∧
      payloadPointer.toNat + payload.toNat < 2^64 ∧ pointer.toNat ≤ payloadPointer.toNat
  have bodyProperty : ∀ value output, evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_rlp_decode_fully) =
      (some (.returned value),output) → property value := by
    intro value output evaluated
    exact rlpDecodeFully_body_range_contract entry output pointer length value pointerLocal lengthLocal code
      (by change 12 ≤ state.clock - 1; omega) inputRange inputBound evaluated
  obtain ⟨value,ready,output,valid,locals,tail,restored⟩ := evaluate_decCall_normal_return_property state post name
    (ofString "rlp_decode_fully") (.comb [.one,.one,.one,.one]) (.comb [.one,.one,.one,.one]) arguments [.val (.word pointer),.val (.word length)]
    (sourceFunctionBody Guest.guestFn_rlp_decode_fully) continuation callee args lookup property bodyProperty run
  obtain ⟨kind,payloadPointer,payload,shape,flag,bounded,positive,rangeBound,rangeNoWrap,rangeStart⟩ := valid
  subst value
  exact ⟨kind,payloadPointer,payload,ready,output,flag,bounded,positive,rangeBound,rangeNoWrap,rangeStart,locals,tail,restored⟩

#print axioms evaluate_rlpDecodeFully_declaration_range
end InitECandidate.Runtime
