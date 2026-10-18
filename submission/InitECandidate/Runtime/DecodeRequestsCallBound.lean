import InitECandidate.Runtime.DecodeRequestsBodyBound
import InitECandidate.Runtime.OriginalDecodeRequestsCode
import InitECandidate.Runtime.PanTwoWordLookup
import InitECandidate.Runtime.CallBodyClockNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual request-decoder call costs at most 355 source ticks,
including entry and every rejection or inaccessible-store/load failure. -/
theorem evaluate_decodeRequests_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (pointer length offsets heapPointer : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (pointerBound : heapPointer.toNat ≤ 33806089496)
    (budget : 355 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "decode_requests") arguments)
    state.clock ≤ evaluated.2.clock + (355) ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update (ofString "len",.val (.word length))
  let entry := callEntryStateHOLFinite state callee
  have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have len : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bounded := evaluate_decodeRequests_body_bounded entry length heapPointer offsets code len heap pointerBound atOffsets
  have lookup := pan_two_word_lookup state.code.lookup (ofString "decode_requests") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_decode_requests) pointer length (by decide)
    (by rw [code]; exact originalRuntimeCode_decodeRequests_lookup)
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_decode_requests) with
  | mk result post =>
    rw [bodyRun] at bounded
    dsimp only at bounded
    have output := evaluate_call_body_clock_no_timeout state post (ofString "decode_requests") destination arguments _
      (sourceFunctionBody Guest.guestFn_decode_requests) callee .one result args lookup (by omega) bodyRun (bounded.2.2 (by change 354 ≤ state.clock - 1; omega))
    dsimp only
    rw [output.2]
    refine ⟨?_,?_,output.1⟩
    · have consumed := bounded.1
      change state.clock - 1 ≤ post.clock + (354) at consumed
      change state.clock ≤ post.clock + (355)
      omega
    · have remaining := bounded.2.1
      change post.clock ≤ state.clock - 1 at remaining
      change post.clock ≤ state.clock
      omega

#print axioms evaluate_decodeRequests_call_bounded
end InitECandidate.Runtime
