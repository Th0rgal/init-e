import InitECandidate.Runtime.RlpUncheckedBodyBound
import InitECandidate.Runtime.OriginalRlpUncheckedCode
import InitECandidate.Runtime.PanSingleWordLookup
import InitECandidate.Runtime.PanDecCallStraightBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual unchecked helper declaration adds one entry tick; a checked
straight-line continuation, including slice stores, adds no source ticks. -/
theorem evaluate_rlpUnchecked_declaration_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (supported : straightLine continuation = true) (pointer : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer)])
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state
      (.decCall name .one (ofString "rlp_item_total_unchecked") arguments continuation)
    state.clock ≤ evaluated.2.clock + 11 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))
  let entry := callEntryStateHOLFinite state callee
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have bound := evaluate_rlpUnchecked_body_bounded entry pointer atPointer code (by change 10 ≤ state.clock - 1; omega)
  cases run : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_rlp_item_total_unchecked) with
  | mk result post =>
    rw [run] at bound
    dsimp only at bound
    have installed : state.code.lookup (ofString "rlp_item_total_unchecked") =
        some ([(ofString "p",.one)],sourceFunctionBody Guest.guestFn_rlp_item_total_unchecked,.one) := by
      rw [code]; exact originalRuntimeCode_rlpUnchecked_lookup
    have lookup := pan_single_word_lookup state.code.lookup (ofString "rlp_item_total_unchecked") (ofString "p")
      (sourceFunctionBody Guest.guestFn_rlp_item_total_unchecked) pointer installed
    have entryClock : entry.clock = state.clock - 1 := rfl
    exact evaluate_decCall_straight_bounded state post name (ofString "rlp_item_total_unchecked") .one .one arguments
      [.val (.word pointer)] (sourceFunctionBody Guest.guestFn_rlp_item_total_unchecked) continuation callee result 11
      args lookup (by omega) run bound.2.1 (by omega) bound.2.2.1 supported

#print axioms evaluate_rlpUnchecked_declaration_bounded
end InitECandidate.Runtime
