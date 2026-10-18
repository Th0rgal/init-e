import InitECandidate.Runtime.DecodeBytesListBody
import InitECandidate.Runtime.PanFourWordShapeLookup
import InitECandidate.Runtime.PanDecCallContinuationBound
import InitECandidate.Runtime.DecodeBytesListReturnedHeap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Compose a byte-list declaration with its real continuation, retaining
the capped heap and nonallocator global frame supplied by any returned body. -/
theorem evaluate_decodeBytesList_declaration_continuation_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (continuation : ProgHOL 64) (tailCost : Nat)
    (arguments : List (ExpHOL 64))
    (pointer length limit maxBytes heapPointer : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length),.val (.word limit),.val (.word maxBytes)])
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496)
    (budget : bytesListBound length + 1 + tailCost ≤ state.clock)
    (continuationBound : ∀ (value : ValueHOL 64) (ready : PanSemStateFiniteExact 64 F) (nextHeap : BitVec 64),
      ready.locals = state.locals.update (name,value) → ready.code = state.code → ready.memaddrs = state.memaddrs →
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) → nextHeap.toNat ≤ 33806089496 →
      (∀ key, key ≠ ofString "heap_ptr" → ready.globals.lookup key = state.globals.lookup key) →
      tailCost ≤ ready.clock →
      let evaluated := evaluateHOLFiniteState ready continuation
      ready.clock ≤ evaluated.2.clock + tailCost ∧ evaluated.2.clock ≤ ready.clock ∧ evaluated.1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state (.decCall name (.comb [.one,.one]) (ofString "decode_bytes_list") arguments continuation)
    state.clock ≤ evaluated.2.clock + (bytesListBound length + 1 + tailCost) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (((HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update
      (ofString "len",.val (.word length))).update (ofString "lim",.val (.word limit))).update
      (ofString "maxb",.val (.word maxBytes))
  let entry := callEntryStateHOLFinite state callee
  have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide,show ofString "lim" ≠ ofString "p" by decide,
      show ofString "maxb" ≠ ofString "p" by decide]
  have len : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "lim" ≠ ofString "len" by decide,show ofString "maxb" ≠ ofString "len" by decide]
  have lim : entry.locals.lookup (ofString "lim") = some (.val (.word limit)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "maxb" ≠ ofString "lim" by decide]
  have maxb : entry.locals.lookup (ofString "maxb") = some (.val (.word maxBytes)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bounded := evaluate_decodeBytesList_body entry pointer length limit maxBytes heapPointer code p len lim maxb heap heapBound
  have lookup := pan_four_word_shape_lookup state.code.lookup (ofString "decode_bytes_list")
    (ofString "p") (ofString "len") (ofString "lim") (ofString "maxb")
    (sourceFunctionBody Guest.guestFn_decode_bytes_list) (.comb [.one,.one]) pointer length limit maxBytes
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [code]; exact originalRuntimeCode_decodeBytesList_lookup)
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_decode_bytes_list)
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_decode_bytes_list) with
  | mk result post =>
    rw [bodyRun] at bounded metadata
    dsimp only at bounded metadata
    have consumed : state.clock ≤ post.clock + (bytesListBound length + 1) := by
      have bodySpent := bounded.1
      change state.clock - 1 ≤ post.clock + bytesListBound length at bodySpent
      omega
    apply evaluate_decCall_continuation_bounded state post name (ofString "decode_bytes_list")
      (.comb [.one,.one]) (.comb [.one,.one]) arguments
      [.val (.word pointer),.val (.word length),.val (.word limit),.val (.word maxBytes)]
      (sourceFunctionBody Guest.guestFn_decode_bytes_list) continuation callee result
      (bytesListBound length + 1) tailCost args lookup (by omega) bodyRun bounded.2.1 consumed
      (bounded.2.2.1 (by change bytesListBound length ≤ state.clock - 1; omega))
    intro value returned
    obtain ⟨nextHeap,nextGlobal,nextBound,other⟩ := decodeBytesList_returned_heap entry post pointer length limit maxBytes
      heapPointer value heap heapBound (bounded.2.2.2.2 value returned)
    let ready := setVarHOLFinite name value {post with locals := state.locals}
    exact continuationBound value ready nextHeap rfl metadata.1 metadata.2.1 nextGlobal nextBound other
      (by change tailCost ≤ post.clock; omega)

#print axioms evaluate_decodeBytesList_declaration_continuation_bounded
end InitECandidate.Runtime
