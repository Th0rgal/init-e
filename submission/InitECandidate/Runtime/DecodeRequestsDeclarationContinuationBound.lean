import InitECandidate.Runtime.DecodeRequestsBodyBound
import InitECandidate.Runtime.DecodeRequestsReturned
import InitECandidate.Runtime.OriginalDecodeRequestsCode
import InitECandidate.Runtime.PanTwoWordLookup
import InitECandidate.Runtime.PanDecCallContinuationBound
import InitECandidate.Runtime.DecodeRequestsReturnedHeap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Compose a request declaration with its real continuation, retaining
the capped heap and nonallocator global frame supplied by any returned body. -/
theorem evaluate_decodeRequests_declaration_continuation_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (continuation : ProgHOL 64) (tailCost : Nat)
    (arguments : List (ExpHOL 64))
    (pointer length offsets heapPointer : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496)
    (budget : 355 + tailCost ≤ state.clock)
    (continuationBound : ∀ (value : ValueHOL 64) (ready : PanSemStateFiniteExact 64 F) (nextHeap : BitVec 64),
      ready.locals = state.locals.update (name,value) → ready.code = state.code → ready.memaddrs = state.memaddrs →
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) → nextHeap.toNat ≤ 33806089496 →
      (∀ key, key ≠ ofString "heap_ptr" → ready.globals.lookup key = state.globals.lookup key) →
      tailCost ≤ ready.clock →
      let evaluated := evaluateHOLFiniteState ready continuation
      ready.clock ≤ evaluated.2.clock + tailCost ∧ evaluated.2.clock ≤ ready.clock ∧ evaluated.1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state (.decCall name .one (ofString "decode_requests") arguments continuation)
    state.clock ≤ evaluated.2.clock + (355 + tailCost) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update
      (ofString "len",.val (.word length))
  let entry := callEntryStateHOLFinite state callee
  have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have len : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bounded := evaluate_decodeRequests_body_bounded entry length heapPointer offsets code len heap heapBound atOffsets
  have lookup := pan_two_word_lookup state.code.lookup (ofString "decode_requests")
    (ofString "p") (ofString "len") (sourceFunctionBody Guest.guestFn_decode_requests) pointer length
    (by decide) (by rw [code]; exact originalRuntimeCode_decodeRequests_lookup)
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_decode_requests)
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_decode_requests) with
  | mk result post =>
    rw [bodyRun] at bounded metadata
    dsimp only at bounded metadata
    have consumed : state.clock ≤ post.clock + (355) := by
      have bodySpent := bounded.1
      change state.clock - 1 ≤ post.clock + 354 at bodySpent
      omega
    apply evaluate_decCall_continuation_bounded state post name (ofString "decode_requests")
      .one .one arguments
      [.val (.word pointer),.val (.word length)]
      (sourceFunctionBody Guest.guestFn_decode_requests) continuation callee result
      (355) tailCost args lookup (by omega) bodyRun bounded.2.1 consumed
      (bounded.2.2 (by change 354 ≤ state.clock - 1; omega))
    intro value returned
    have returnedFacts := evaluate_decodeRequests_returned entry pointer length heapPointer offsets code
      p len heap heapBound atOffsets value (by rw [bodyRun]; exact returned)
    rw [bodyRun] at returnedFacts
    obtain ⟨nextHeap,nextGlobal,nextBound,other⟩ := decodeRequests_returned_heap entry post pointer length
      heapPointer offsets value heapBound returnedFacts
    let ready := setVarHOLFinite name value {post with locals := state.locals}
    exact continuationBound value ready nextHeap rfl metadata.1 metadata.2.1 nextGlobal nextBound other
      (by change tailCost ≤ post.clock; omega)

#print axioms evaluate_decodeRequests_declaration_continuation_bounded
end InitECandidate.Runtime
