import InitECandidate.Runtime.RlpHeaderUniformResult
import InitECandidate.Runtime.OriginalRlpHeaderCode
import InitECandidate.Runtime.PanTwoWordShapeLookup
import InitECandidate.Runtime.DiscardCallNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpHeaderCallee (pointer length : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  (HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update (ofString "len",.val (.word length))

/-- The original header-reader call costs at most twelve ticks, including
canonicality exceptions and failed input reads. -/
theorem evaluate_rlpHeader_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer length : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (code : state.code = originalRuntimeCode) (ticks : 12 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_item_header") arguments)
    state.clock ≤ evaluated.2.clock + 12 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have pointerLocal : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have lengthLocal : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨bodyResult,bodyPost,bodyRun,cost,remaining,noTimeout,_,_⟩ := evaluate_rlpHeader_uniform_contract entry pointer length
    pointerLocal lengthLocal code (by change 11 ≤ state.clock - 1; omega)
  have installed : state.code.lookup (ofString "rlp_item_header") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_item_header,.comb [.one,.one,.one]) := by
    rw [code]; exact originalRuntimeCode_rlpHeader_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_item_header")
    (ofString "p") (ofString "len") (sourceFunctionBody Guest.guestFn_rlp_item_header) (.comb [.one,.one,.one]) pointer length (by decide) installed
  have clock := evaluate_discard_call_body_clock state bodyPost (ofString "rlp_item_header") arguments
    [.val (.word pointer),.val (.word length)] (sourceFunctionBody Guest.guestFn_rlp_item_header)
    callee (.comb [.one,.one,.one]) bodyResult args lookup (by omega) bodyRun
  have safe := evaluate_discard_call_body_no_timeout state bodyPost (ofString "rlp_item_header") arguments
    [.val (.word pointer),.val (.word length)] (sourceFunctionBody Guest.guestFn_rlp_item_header)
    callee (.comb [.one,.one,.one]) bodyResult args lookup (by omega) bodyRun noTimeout
  dsimp only
  rw [clock]
  have entryClock : entry.clock = state.clock - 1 := rfl
  exact ⟨by omega,by omega,safe⟩

#print axioms evaluate_rlpHeader_call_bounded
end InitECandidate.Runtime
