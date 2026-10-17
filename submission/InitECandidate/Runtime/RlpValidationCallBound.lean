import InitECandidate.Runtime.RlpValidationBodyBound
import InitECandidate.Runtime.OriginalRlpValidationCode
import InitECandidate.Runtime.DiscardCallNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original validator body call adds one call tick to the proved
input-length body budget, retaining failure and no-timeout coverage. -/
theorem evaluate_rlpValidation_body_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : (2 * length.toNat + 1) * 15 + 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "_rlp_validate_items_body") arguments)
    state.clock ≤ evaluated.2.clock + ((2 * length.toNat + 1) * 15 + 1) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have pointerLocal : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have lengthLocal : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have bound := evaluate_rlpValidation_body_bounded entry pointer length scratch frame ceiling inputLimit
    pointerLocal lengthLocal noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
    scratchBelow arena (by change (2 * length.toNat + 1) * 15 ≤ state.clock - 1; omega)
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn__rlp_validate_items_body) with
  | mk bodyResult bodyPost =>
    rw [bodyRun] at bound
    dsimp only at bound
    have installed : state.code.lookup (ofString "_rlp_validate_items_body") =
        some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn__rlp_validate_items_body,.one) := by
      rw [code]; exact originalRuntimeCode_rlpValidationBody_lookup
    have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "_rlp_validate_items_body")
      (ofString "p") (ofString "len") (sourceFunctionBody Guest.guestFn__rlp_validate_items_body) .one pointer length (by decide) installed
    have clock := evaluate_discard_call_body_clock state bodyPost (ofString "_rlp_validate_items_body") arguments
      [.val (.word pointer),.val (.word length)] (sourceFunctionBody Guest.guestFn__rlp_validate_items_body)
      callee .one bodyResult args lookup (by omega) bodyRun
    have safe := evaluate_discard_call_body_no_timeout state bodyPost (ofString "_rlp_validate_items_body") arguments
      [.val (.word pointer),.val (.word length)] (sourceFunctionBody Guest.guestFn__rlp_validate_items_body)
      callee .one bodyResult args lookup (by omega) bodyRun bound.2.2.1
    dsimp only
    rw [clock]
    have entryClock : entry.clock = state.clock - 1 := rfl
    exact ⟨by omega,by omega,safe⟩

#print axioms evaluate_rlpValidation_body_call_bounded
end InitECandidate.Runtime
