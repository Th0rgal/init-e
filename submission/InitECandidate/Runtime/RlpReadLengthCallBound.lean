import InitECandidate.Runtime.RlpReadLengthCallResult
import InitECandidate.Runtime.DiscardCallNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original length-reader call costs at most n+2 ticks, including
canonicality exceptions and failed input reads. -/
theorem evaluate_rlpReadLength_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer length : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (code : state.code = originalRuntimeCode) (ticks : length.toNat + 2 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_read_length") arguments)
    state.clock ≤ evaluated.2.clock + (length.toNat + 2) ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let callee := rlpReadLengthCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have pointerLocal : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpReadLengthCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "n" ≠ ofString "p" by decide]
  have lengthLocal : entry.locals.lookup (ofString "n") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpReadLengthCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨bodyResult,bodyPost,bodyRun,cost,remaining,noTimeout,_⟩ := evaluate_rlpReadLength_body_bounded entry pointer length
    pointerLocal lengthLocal code (by change length.toNat + 1 ≤ state.clock - 1; omega)
  have installed : state.code.lookup (ofString "rlp_read_length") =
      some ([(ofString "p",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_rlp_read_length,.one) := by
    rw [code]; exact originalRuntimeCode_rlpReadLength_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "rlp_read_length")
    (ofString "p") (ofString "n") (sourceFunctionBody Guest.guestFn_rlp_read_length) pointer length (by decide) installed
  have clock := evaluate_discard_call_body_clock state bodyPost (ofString "rlp_read_length") arguments
    [.val (.word pointer),.val (.word length)] (sourceFunctionBody Guest.guestFn_rlp_read_length)
    callee .one bodyResult args lookup (by omega) bodyRun
  have safe := evaluate_discard_call_body_no_timeout state bodyPost (ofString "rlp_read_length") arguments
    [.val (.word pointer),.val (.word length)] (sourceFunctionBody Guest.guestFn_rlp_read_length)
    callee .one bodyResult args lookup (by omega) bodyRun noTimeout
  dsimp only
  rw [clock]
  have entryClock : entry.clock = state.clock - 1 := rfl
  exact ⟨by omega,by omega,safe⟩

#print axioms evaluate_rlpReadLength_call_bounded
end InitECandidate.Runtime
