import InitECandidate.Runtime.RlpSliceInputPrefixAbove
import InitECandidate.Runtime.RlpDecodeFullyBodyAbove
import InitECandidate.Runtime.TransactionMemzeroLowerFrame
import InitECandidate.Runtime.PanLocalCallNormalResult
import InitECandidate.Runtime.OriginalRlpDecodeFullyCode
import InitECandidate.Runtime.PanTwoWordShapeLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpDecodeFully_local_call_above {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (run : evaluateHOLFiniteState state (.call (some (some (.local,name),none)) (ofString "rlp_decode_fully") arguments) = (none,post)) (address : BitVec 64) (above : ceiling ≤ address.toNat) :
    post.memory address = state.memory address := by
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
  have memory := rlpDecodeFully_body_returned_above entry bodyPost pointer length scratch frame ceiling inputLimit
    atPointer atLength inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena ticks
    value bodyRun address above
  rw [restored]
  exact memory

theorem rlpDecodeFully_local_call_heap_input_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (array count input inputLength : BitVec 64)
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (above : ceiling ≤ array.toNat)
    (run : evaluateHOLFiniteState state (.call (some (some (.local,name),none)) (ofString "rlp_decode_fully") arguments) = (none,post)) :
    RlpSliceInputPrefix post array input inputLength count.toNat := by
  have metadata := evaluateHOLFiniteState_metadata state
    (.call (some (some (.local,name),none)) (ofString "rlp_decode_fully") arguments)
  rw [run] at metadata
  exact RlpSliceInputPrefix.after_memory_above state post array count input inputLength valid fits metadata.2.1
    (fun address above => rlpDecodeFully_local_call_above state post name arguments pointer length scratch frame ceiling inputLimit
      args inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget run address (by omega))

#print axioms rlpDecodeFully_local_call_heap_input_prefix
#print axioms rlpDecodeFully_local_call_above
end InitECandidate.Runtime
