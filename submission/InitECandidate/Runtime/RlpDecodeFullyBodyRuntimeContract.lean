import InitECandidate.Runtime.RlpDecodeFullyBodyGlobals
import InitECandidate.Runtime.RlpDecodeFullyBodyNamedGlobal
import InitECandidate.Runtime.RlpDecodeFullyBodyRange
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpDecodeFully_body_returned_runtime_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92633 ≤ state.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_decode_fully) = (some (.returned value),post)) :
    ∃ kind payloadPointer payload : BitVec 64,
      value = .rStruct [.val (.word kind),.val (.word payloadPointer),.val (.word payload),.val (.word length)] ∧
      (kind = 0 ∨ kind = 1) ∧ payload.toNat ≤ length.toNat ∧ 0 < length.toNat ∧
      payloadPointer.toNat + payload.toNat ≤ pointer.toNat + length.toNat ∧
      payloadPointer.toNat + payload.toNat < 2^64 ∧ pointer.toNat ≤ payloadPointer.toNat ∧
      (∀ watched, post.globals.lookup watched = state.globals.lookup watched) := by
  obtain ⟨kind,payloadPointer,payload,shape,flag,bounded,positive,ends,noWrap,starts⟩ :=
    rlpDecodeFully_body_range_contract state post pointer length value pointerLocal lengthLocal code (by omega) inputRange (by omega) run
  have restored := rlpDecodeFully_body_returned_globals state post pointer length scratch frame ceiling inputLimit
    pointerLocal lengthLocal inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget value run
  refine ⟨kind,payloadPointer,payload,shape,flag,bounded,positive,ends,noWrap,starts,?_⟩
  intro watched
  by_cases same : watched = ofString "scratch_ptr"
  · subst watched
    exact restored.1.trans scratchGlobal.symm
  · exact rlpDecodeFully_body_returned_named_global state post watched (Ne.symm same) pointer length scratch frame ceiling inputLimit
      pointerLocal lengthLocal inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget value run

#print axioms rlpDecodeFully_body_returned_runtime_contract
end InitECandidate.Runtime
