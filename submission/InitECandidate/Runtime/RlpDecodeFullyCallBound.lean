import InitECandidate.Runtime.RlpDecodeFullyLocalCallRuntimeContract
import InitECandidate.Runtime.RlpDecodeFullyBodyBound
import InitECandidate.Runtime.CallBodyClockNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_rlpDecodeFully_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
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
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92635 ≤ state.clock) :
    let output := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "rlp_decode_fully") arguments)
    state.clock ≤ output.2.clock + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92635) ∧
      output.2.clock ≤ state.clock ∧ output.1 ≠ some .timeOut := by
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
  have bound := evaluate_rlpDecodeFully_body_bounded entry pointer length scratch frame ceiling inputLimit
    atPointer atLength inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    (by change length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92634 ≤ state.clock - 1; omega)
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_rlp_decode_fully) with
  | mk result post =>
    rw [bodyRun] at bound
    dsimp only at bound
    have entryClock : entry.clock = state.clock - 1 := rfl
    have output := evaluate_call_body_clock_no_timeout state post (ofString "rlp_decode_fully") destination arguments _
      (sourceFunctionBody Guest.guestFn_rlp_decode_fully) callee (.comb [.one,.one,.one,.one]) result args lookup (by omega) bodyRun bound.2.2
    dsimp only
    rw [output.2]
    exact ⟨by omega,by omega,output.1⟩

#print axioms evaluate_rlpDecodeFully_call_bounded
end InitECandidate.Runtime
