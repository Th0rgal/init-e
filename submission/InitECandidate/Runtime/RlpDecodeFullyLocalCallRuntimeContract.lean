import InitECandidate.Runtime.RlpDecodeFullyBodyRuntimeContract
import InitECandidate.Runtime.PanLocalCallNormalResult
import InitECandidate.Runtime.OriginalRlpDecodeFullyCode
import InitECandidate.Runtime.PanTwoWordShapeLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpDecodeFully_local_call_runtime_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (arguments : List (ExpHOL 64))
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92634 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (some (.local,name),none)) (ofString "rlp_decode_fully") arguments) = (none,post)) :
    ∃ kind payloadPointer payload : BitVec 64,
      post.locals.lookup name = some (.rStruct [.val (.word kind),.val (.word payloadPointer),.val (.word payload),.val (.word length)]) ∧
      (kind = 0 ∨ kind = 1) ∧ payload.toNat ≤ length.toNat ∧ 0 < length.toNat ∧
      payloadPointer.toNat + payload.toNat ≤ pointer.toNat + length.toNat ∧
      payloadPointer.toNat + payload.toNat < 2^64 ∧ pointer.toNat ≤ payloadPointer.toNat ∧
      (∀ watched, post.globals.lookup watched = state.globals.lookup watched) := by
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callee,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have installed : state.code.lookup (ofString "rlp_decode_fully") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_decode_fully,.comb [.one,.one,.one,.one]) := by
    rw [code]; exact originalRuntimeCode_rlpDecodeFully_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_decode_fully") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_rlp_decode_fully) (.comb [.one,.one,.one,.one]) pointer length (by decide) installed
  obtain ⟨value,bodyPost,bodyRun,checked,restored⟩ := evaluate_localCall_normal_result state post name (ofString "rlp_decode_fully")
    (.comb [.one,.one,.one,.one]) arguments _ _ callee args lookup run
  have ticks : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92633 ≤ entry.clock := by
    change _ ≤ state.clock - 1
    omega
  obtain ⟨kind,payloadPointer,payload,shape,flag,bounded,positive,ends,noWrap,starts,globals⟩ :=
    rlpDecodeFully_body_returned_runtime_contract entry bodyPost pointer length scratch frame ceiling inputLimit
      atPointer atLength inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena ticks value bodyRun
  refine ⟨kind,payloadPointer,payload,?_,flag,bounded,positive,ends,noWrap,starts,?_⟩
  · rw [restored]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,shape]
  · rw [restored]
    exact globals

#print axioms rlpDecodeFully_local_call_runtime_contract
end InitECandidate.Runtime
