import InitECandidate.Runtime.RlpItemBodyBound
import InitECandidate.Runtime.OriginalRlpItemCode
import InitECandidate.Runtime.RlpDecodeFullyContinuation
import InitECandidate.Runtime.PanDecCallContinuationBound
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete original full decoder adds one item-call tick and at
most one length-check rejection tick to the item body budget. -/
theorem evaluate_rlpDecodeFully_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92634 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_decode_fully)
    state.clock ≤ evaluated.2.clock + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92634) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  let arguments : List (ExpHOL 64) := [.var .local (ofString "p"),.var .local (ofString "len")]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)] := by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atPointer,atLength]
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have pointerLocal : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have lengthLocal : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have bound := evaluate_rlpItem_body_bounded entry pointer length scratch frame ceiling inputLimit
    pointerLocal lengthLocal noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
    scratchBelow arena (by change length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92632 ≤ state.clock - 1; omega)
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_rlp_item) with
  | mk bodyResult bodyPost =>
    rw [bodyRun] at bound
    dsimp only at bound
    have installed : state.code.lookup (ofString "rlp_item") =
        some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_item,.comb [.one,.one,.one,.one]) := by
      rw [code]; exact originalRuntimeCode_rlpItem_lookup
    have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_item")
      (ofString "p") (ofString "len") (sourceFunctionBody Guest.guestFn_rlp_item) (.comb [.one,.one,.one,.one]) pointer length (by decide) installed
    have entryClock : entry.clock = state.clock - 1 := rfl
    have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_item)
    rw [bodyRun] at metadata
    dsimp only at metadata
    have continuationBound : ∀ value, bodyResult = some (.returned value) →
        let resumed := setVarHOLFinite (ofString "it") value {bodyPost with locals := state.locals}
        let evaluated := evaluateHOLFiniteState resumed rlpDecodeFullyContinuation
        resumed.clock ≤ evaluated.2.clock + 1 ∧ evaluated.2.clock ≤ resumed.clock ∧ evaluated.1 ≠ some .timeOut := by
      intro value equal
      exact evaluate_rlpDecodeFully_continuation_bounded _ (metadata.1.trans code)
        (by change 1 ≤ bodyPost.clock; omega)
    have composed := evaluate_decCall_continuation_bounded state bodyPost (ofString "it") (ofString "rlp_item")
      (.comb [.one,.one,.one,.one]) (.comb [.one,.one,.one,.one]) arguments
      [.val (.word pointer),.val (.word length)] (sourceFunctionBody Guest.guestFn_rlp_item)
      rlpDecodeFullyContinuation callee bodyResult
      (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92633) 1
      args lookup (by omega) bodyRun bound.2.1 (by omega) bound.2.2 continuationBound
    rw [source_rlpDecodeFully_body]
    change state.clock ≤ (evaluateHOLFiniteState state (.decCall _ _ _ arguments _)).2.clock + _ ∧ _
    dsimp only at composed ⊢
    exact ⟨by omega,composed.2⟩

#print axioms evaluate_rlpDecodeFully_body_bounded
end InitECandidate.Runtime
