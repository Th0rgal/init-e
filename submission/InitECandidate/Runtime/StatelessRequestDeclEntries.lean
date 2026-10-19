import InitECandidate.Runtime.StatelessWitnessRequestEntries
import InitECandidate.Runtime.StatelessRequestsWitnessReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual request-decoder declaration exports its fresh request table,
including readable entries and their input-derived count bounds. -/
theorem ret_requestsDecl_entries {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (args : List (ExpHOL 64)) (rest : ProgHOL 64)
    (pointer length record offsets : BitVec 64) (value : ValueHOL 64)
    (code : state.code = originalRuntimeCode)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) args =
      some [.val (.word pointer),.val (.word length)])
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word record)))
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heapBound : record.toNat ≤ 33806089496) (small : length.toNat ≤ 134217712)
    (run : evaluateHOLFiniteState state (.decCall name .one (ofString "decode_requests") args rest) =
      (some (.returned value),post)) :
    ∃ ready output : PanSemStateFiniteExact 64 F,
      (∀ key, key ≠ name → ready.locals.lookup key = state.locals.lookup key) ∧
      ready.locals.lookup name = some (.val (.word record)) ∧ ready.code = state.code ∧
      ready.memaddrs = state.memaddrs ∧ HtrRequestsDecoded ready record ∧
      (∃ heap : BitVec 64, ready.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
        record.toNat + 80 ≤ heap.toNat ∧ heap.toNat ≤ 33806089496 ∧ heap.toNat % 8 = 0) ∧
      (∀ key, key ≠ ofString "heap_ptr" → ready.globals.lookup key = state.globals.lookup key) ∧
      evaluateHOLFiniteState ready rest = (some (.returned value),output) ∧
      post.memory = output.memory ∧ post.memaddrs = output.memaddrs := by
  have different : ofString "p" ≠ ofString "len" := by decide_cbv
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "decode_requests") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_decode_requests) .one pointer length different
    (by rw [code]; exact originalRuntimeCode_decodeRequests_lookup)
  obtain ⟨returned,bodyPost,output,bodyRun,_,tail,postEq⟩ :=
    evaluate_decCall_checked_returned_exact_scope state post name (ofString "decode_requests") .one .one
      args _ _ rest _ value arguments lookup run
  generalize entryEq : callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update
      (ofString "len",.val (.word length))) = entry at bodyRun
  have entryCode : entry.code = originalRuntimeCode := by rw [← entryEq]; exact code
  have entryPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    rw [← entryEq]; simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have entryLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    rw [← entryEq]; simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryHeap : entry.globals.lookup (ofString "heap_ptr") = some (.val (.word record)) := by
    rw [← entryEq]; exact atHeap
  have entryOffsets : entry.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)) := by
    rw [← entryEq]; exact atOffsets
  have decoded := htrRequestsDecoded_of_decodeRequests_returned entry bodyPost pointer length record offsets returned
    entryCode entryPointer entryLength entryHeap heapBound entryOffsets small bodyRun
  have facts := evaluate_decodeRequests_returned entry pointer length record offsets entryCode entryPointer entryLength
    entryHeap heapBound entryOffsets returned (by rw [bodyRun])
  rw [bodyRun] at facts
  obtain ⟨_,_,_,_,facts⟩ := facts
  obtain ⟨allocation,hvalue,_,_,_,_,_,_,_,_,_,_,_,_,globals,_⟩ := facts
  subst hvalue
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_decode_requests)
  rw [bodyRun] at metadata
  have sum := allocationGuard_sum_bound record 80 heapBound allocation
  have covers := allocationEnd_covers record 80 sum
  change record.toNat + 80 ≤ (allocationEnd record 80).toNat ∧ _ at covers
  refine ⟨setVarHOLFinite name (.val (.word record)) {bodyPost with locals := state.locals},output,?_,?_,?_,?_,?_,?_,?_,tail,?_,?_⟩
  · intro key different; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · show bodyPost.code = state.code; rw [metadata.1,← entryEq]; rfl
  · show bodyPost.memaddrs = state.memaddrs; rw [metadata.2.1,← entryEq]; rfl
  · exact decoded.after_frame rfl rfl
  · refine ⟨allocationEnd record 80,?_,by omega,allocationEnd_within_heap record 80 heapBound allocation,covers.2.2⟩
    show bodyPost.globals.lookup _ = _
    rw [globals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro key different
    show bodyPost.globals.lookup key = state.globals.lookup key
    rw [globals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,← entryEq]
    rfl
  · rw [postEq]
  · rw [postEq]

#print axioms ret_requestsDecl_entries
end InitECandidate.Runtime
