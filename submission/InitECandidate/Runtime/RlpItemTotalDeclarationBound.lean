import InitECandidate.Runtime.RlpItemTotalBodyBound
import InitECandidate.Runtime.OriginalRlpItemTotalCode
import InitECandidate.Runtime.PanDecCallStraightBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original item-total declaration with a straight-line continuation
has an input-linear budget across all successful and failed outcomes. -/
theorem evaluate_rlpItemTotal_declaration_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (continuation : ProgHOL 64) (supported : straightLine continuation = true)
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
    (budget : (2 * length.toNat + 1) * 15 + 18 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.decCall name .one (ofString "rlp_item_total") arguments continuation)
    state.clock ≤ evaluated.2.clock + ((2 * length.toNat + 1) * 15 + 18) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have pointerLocal : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have lengthLocal : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have bound := evaluate_rlpItemTotal_body_bounded entry pointer length scratch frame ceiling inputLimit
    pointerLocal lengthLocal noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
    scratchBelow arena (by change (2 * length.toNat + 1) * 15 + 17 ≤ state.clock - 1; omega)
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_rlp_item_total) with
  | mk bodyResult bodyPost =>
    rw [bodyRun] at bound
    dsimp only at bound
    have installed : state.code.lookup (ofString "rlp_item_total") =
        some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_item_total,.one) := by
      rw [code]; exact originalRuntimeCode_rlpItemTotal_lookup
    have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_item_total")
      (ofString "p") (ofString "len") (sourceFunctionBody Guest.guestFn_rlp_item_total) .one pointer length (by decide) installed
    have entryClock : entry.clock = state.clock - 1 := rfl
    exact evaluate_decCall_straight_bounded state bodyPost name (ofString "rlp_item_total") .one .one arguments
      [.val (.word pointer),.val (.word length)] (sourceFunctionBody Guest.guestFn_rlp_item_total) continuation callee bodyResult
      ((2 * length.toNat + 1) * 15 + 18) args lookup (by omega) bodyRun bound.2.1
      (by omega) bound.2.2 supported

#print axioms evaluate_rlpItemTotal_declaration_bounded
end InitECandidate.Runtime
