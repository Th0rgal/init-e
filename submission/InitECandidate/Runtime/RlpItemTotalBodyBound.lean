import InitECandidate.Runtime.RlpItemTotalContinuation
import InitECandidate.Runtime.RlpValidationHeaderBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_rlpItemTotal_body : sourceFunctionBody Guest.guestFn_rlp_item_total =
    .decCall (ofString "h") (.comb [.one,.one,.one]) (ofString "rlp_item_header")
      [.var .local (ofString "p"),.var .local (ofString "len")] rlpItemTotalContinuation := by
  simp only [rlpItemTotalContinuation,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Complete original item-total body, including bounded header parsing,
recursive list validation, failures and return of the consumed byte count. -/
theorem evaluate_rlpItemTotal_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : (2 * length.toNat + 1) * 15 + 17 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item_total)
    state.clock ≤ evaluated.2.clock + ((2 * length.toNat + 1) * 15 + 17) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  let arguments : List (ExpHOL 64) := [.var .local (ofString "p"),.var .local (ofString "len")]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)] := by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,lengthLocal]
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have calleePointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have calleeLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryTicks : 11 ≤ entry.clock := by change 11 ≤ state.clock - 1; omega
  obtain ⟨bodyResult,bodyPost,bodyRun,cost,remaining,noTimeout,_,returned⟩ := evaluate_rlpHeader_uniform_contract
    entry pointer length calleePointer calleeLength code entryTicks
  have installed : state.code.lookup (ofString "rlp_item_header") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_item_header,.comb [.one,.one,.one]) := by
    rw [code]; exact originalRuntimeCode_rlpHeader_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_item_header")
    (ofString "p") (ofString "len") (sourceFunctionBody Guest.guestFn_rlp_item_header) (.comb [.one,.one,.one])
    pointer length (by decide) installed
  have entryClock : entry.clock = state.clock - 1 := rfl
  have totalCost : state.clock ≤ bodyPost.clock + 12 := by omega
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_item_header)
  rw [bodyRun] at metadata
  have tailBound : ∀ value, bodyResult = some (.returned value) →
      let resumed := setVarHOLFinite (ofString "h") value {bodyPost with locals := state.locals}
      let evaluated := evaluateHOLFiniteState resumed rlpItemTotalContinuation
      resumed.clock ≤ evaluated.2.clock + ((2 * length.toNat + 1) * 15 + 5) ∧
        evaluated.2.clock ≤ resumed.clock ∧ evaluated.1 ≠ some .timeOut := by
    intro value success
    have evaluated : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_rlp_item_header) =
        (some (.returned value),bodyPost) := by rw [bodyRun,success]
    have sized : RlpHeaderSizedProgress value length :=
      ⟨returned value success,rlpHeader_uniform_return_sizes entry bodyPost pointer length value
        calleePointer calleeLength code entryTicks evaluated⟩
    have globals := rlpHeader_uniform_returned_globals entry bodyPost pointer length value
      calleePointer calleeLength code entryTicks evaluated
    obtain ⟨header,payload,kind,shape,_,_,_⟩ := sized.2
    subst value
    let resumed := setVarHOLFinite (ofString "h")
      (.rStruct [.val (.word header),.val (.word payload),.val (.word kind)]) {bodyPost with locals := state.locals}
    apply evaluate_rlpItemTotal_continuation_bounded resumed pointer length header payload kind scratch frame ceiling inputLimit
    · simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
        show ofString "h" ≠ ofString "p" by decide] using pointerLocal
    · simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · exact sized
    · exact noWrap
    · exact lengthBound
    · exact limitBound
    · change bodyPost.globals.lookup _ = _
      rw [globals]; exact scratchGlobal
    · change bodyPost.globals.lookup _ = _
      rw [globals]; exact frameGlobal
    · exact metadata.1.trans code
    · exact orderedFrame
    · exact framePositive
    · exact scratchBelow
    · intro address lower upper
      change bodyPost.memaddrs address
      rw [metadata.2.1]
      exact arena address lower upper
    · change (2 * length.toNat + 1) * 15 + 5 ≤ bodyPost.clock
      omega
  rw [source_rlpItemTotal_body]
  have composed := evaluate_decCall_continuation_bounded state bodyPost (ofString "h") (ofString "rlp_item_header")
    (.comb [.one,.one,.one]) (.comb [.one,.one,.one]) arguments [.val (.word pointer),.val (.word length)]
    (sourceFunctionBody Guest.guestFn_rlp_item_header) rlpItemTotalContinuation callee bodyResult 12 ((2 * length.toNat + 1) * 15 + 5)
    args lookup (by omega) bodyRun remaining totalCost noTimeout tailBound
  dsimp only [arguments] at composed ⊢
  exact ⟨by omega,composed.2.1,composed.2.2⟩

#print axioms evaluate_rlpItemTotal_body_bounded
end InitECandidate.Runtime
