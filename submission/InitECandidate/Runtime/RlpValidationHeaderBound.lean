import InitECandidate.Runtime.RlpValidationContinuationBound
import InitECandidate.Runtime.RlpHeaderUniformGlobals
import InitECandidate.Runtime.PanDecCallContinuationBound
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual validator header call has a fourteen-tick budget across header
failures, both parsed item kinds, allocator rejection, and failed stores. -/
theorem evaluate_rlpValidation_header_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (position stop scratch frame : BitVec 64)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (ticks : 14 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpValidationHeaderCall
    state.clock ≤ evaluated.2.clock + 14 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let arguments : List (ExpHOL 64) := [.var .local (ofString "pos"),
    .op .sub [.var .local (ofString "end"),.var .local (ofString "pos")]]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word position),.val (.word (stop - position))] := by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,positionLocal,stopLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  let callee := rlpHeaderCallee position (stop - position)
  let entry := callEntryStateHOLFinite state callee
  have pointerLocal : entry.locals.lookup (ofString "p") = some (.val (.word position)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have lengthLocal : entry.locals.lookup (ofString "len") = some (.val (.word (stop - position))) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryTicks : 11 ≤ entry.clock := by change 11 ≤ state.clock - 1; omega
  obtain ⟨bodyResult,bodyPost,bodyRun,cost,remaining,noTimeout,_,returned⟩ := evaluate_rlpHeader_uniform_contract
    entry position (stop - position) pointerLocal lengthLocal code entryTicks
  have installed : state.code.lookup (ofString "rlp_item_header") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_item_header,.comb [.one,.one,.one]) := by
    rw [code]; exact originalRuntimeCode_rlpHeader_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_item_header")
    (ofString "p") (ofString "len") (sourceFunctionBody Guest.guestFn_rlp_item_header) (.comb [.one,.one,.one])
    position (stop - position) (by decide) installed
  have entryClock : entry.clock = state.clock - 1 := rfl
  have totalCost : state.clock ≤ bodyPost.clock + 12 := by omega
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_item_header)
  rw [bodyRun] at metadata
  have tailBound : ∀ value, bodyResult = some (.returned value) →
      let resumed := setVarHOLFinite (ofString "h") value {bodyPost with locals := state.locals}
      let evaluated := evaluateHOLFiniteState resumed rlpValidationHeaderContinuation
      resumed.clock ≤ evaluated.2.clock + 2 ∧ evaluated.2.clock ≤ resumed.clock ∧ evaluated.1 ≠ some .timeOut := by
    intro value success
    have evaluated : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_rlp_item_header) =
        (some (.returned value),bodyPost) := by rw [bodyRun,success]
    have sized : RlpHeaderSizedProgress value (stop - position) :=
      ⟨returned value success,rlpHeader_uniform_return_sizes entry bodyPost position (stop - position) value
        pointerLocal lengthLocal code entryTicks evaluated⟩
    have globals := rlpHeader_uniform_returned_globals entry bodyPost position (stop - position) value
      pointerLocal lengthLocal code entryTicks evaluated
    apply evaluate_rlpValidation_sized_continuation_bounded {bodyPost with locals := state.locals}
      position (stop - position) scratch frame value sized positionLocal
    · change bodyPost.globals.lookup _ = _
      rw [globals]; exact scratchGlobal
    · change bodyPost.globals.lookup _ = _
      rw [globals]; exact frameGlobal
    · exact metadata.1.trans code
    · change 2 ≤ bodyPost.clock
      omega
  rw [source_rlpValidation_header_call]
  exact evaluate_decCall_continuation_bounded state bodyPost (ofString "h") (ofString "rlp_item_header")
    (.comb [.one,.one,.one]) (.comb [.one,.one,.one]) arguments [.val (.word position),.val (.word (stop - position))]
    (sourceFunctionBody Guest.guestFn_rlp_item_header) rlpValidationHeaderContinuation callee bodyResult 12 2
    args lookup (by omega) bodyRun remaining totalCost noTimeout tailBound

#print axioms evaluate_rlpValidation_header_bounded
end InitECandidate.Runtime
