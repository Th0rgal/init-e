import InitECandidate.Runtime.RlpSlicesBodyBound
import InitECandidate.Runtime.OriginalRlpSlicesCode
import InitECandidate.Runtime.DiscardCallNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original slice-building discard call adds one call tick to the proved
quadratic body budget, including malformed-input and failure outcomes. -/
theorem evaluate_rlpSlices_discard_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 4 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_list_to_slices") arguments)
    state.clock ≤ evaluated.2.clock + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 4) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have pointerLocal : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have lengthLocal : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have bound := evaluate_rlpSlices_body_bounded entry pointer length scratch frame ceiling inputLimit
    pointerLocal lengthLocal noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
    scratchBelow arena (by change length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 3 ≤ state.clock - 1; omega)
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) with
  | mk bodyResult bodyPost =>
    rw [bodyRun] at bound
    dsimp only at bound
    have installed : state.code.lookup (ofString "rlp_list_to_slices") =
        some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_list_to_slices,(.comb [.one,.one])) := by
      rw [code]; exact originalRuntimeCode_rlpSlices_lookup
    have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_list_to_slices")
      (ofString "p") (ofString "len") (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) (.comb [.one,.one]) pointer length (by decide) installed
    have clock := evaluate_discard_call_body_clock state bodyPost (ofString "rlp_list_to_slices") arguments
      [.val (.word pointer),.val (.word length)] (sourceFunctionBody Guest.guestFn_rlp_list_to_slices)
      callee (.comb [.one,.one]) bodyResult args lookup (by omega) bodyRun
    have safe := evaluate_discard_call_body_no_timeout state bodyPost (ofString "rlp_list_to_slices") arguments
      [.val (.word pointer),.val (.word length)] (sourceFunctionBody Guest.guestFn_rlp_list_to_slices)
      callee (.comb [.one,.one]) bodyResult args lookup (by omega) bodyRun bound.2.2
    dsimp only
    rw [clock]
    have entryClock : entry.clock = state.clock - 1 := rfl
    exact ⟨by omega,by omega,safe⟩

#print axioms evaluate_rlpSlices_discard_call_bounded
end InitECandidate.Runtime
