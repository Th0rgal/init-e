import InitECandidate.Runtime.HtrNewPayloadReturnedHeap
import InitECandidate.Runtime.HtrPayloadGlobals
import InitECandidate.Runtime.HtrRequestsGlobals
import InitECandidate.Runtime.MerkleHeapGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The original initial hash preserves every non-heap global on continuing paths. -/
theorem htrNewPayload_normal_heapGlobals : NormalRel HeapGlobalsRel
    (sourceFunctionBody Guest.guestFn_htr_new_payload_request) := by
  have pre := heapGlobalsRel_preorder
  rw [sourceFunctionBody_eq_structural]
  change NormalRel HeapGlobalsRel (htrNewPayloadAt 0)
  rw [source_htrNewPayload_mark]
  apply normalRel_decCall pre _ _ _ _ _ _ _ vmLookup_heap_mark
    (NormalRel.returned (normalRel_readOnly pre heapMark_readOnly))
  rw [source_htrNewPayload_alloc]
  apply normalRel_decCall pre _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup alloc_returned_heapGlobals
  rw [source_htrNewPayload_payload]
  apply normalRel_seq pre (htrPayload_call_heapGlobals _)
  rw [source_htrNewPayload_blobs]
  apply normalRel_seq pre (htrPlistChunks_call_heapGlobals _)
  rw [source_htrNewPayload_copy]
  apply normalRel_seq pre (normalRel_of_frame pre (memcpy_call_globals_frame _))
  rw [source_htrNewPayload_requests]
  apply normalRel_seq pre (htrRequests_call_heapGlobals _)
  rw [source_htrNewPayload_merkle]
  apply normalRel_seq pre (merkleize_call_heapGlobals _)
  rw [source_htrNewPayload_finish]
  apply normalRel_seq pre
    (normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_heap_release_lookup heapRelease_returned_heapGlobals)
  exact normalRel_of_frame pre (originalGlobalsFrame_leaf _ (by intro watched; rfl))

theorem htrNewPayload_call_heapGlobals (arguments : List (ExpHOL 64)) :
    NormalRel HeapGlobalsRel (.call (some (none,none)) (ofString "htr_new_payload_request") arguments) :=
  normalRel_discard_call heapGlobalsRel_preorder _ _ _ _ _ originalRuntimeCode_htrNewPayload_lookup
    (NormalRel.returned htrNewPayload_normal_heapGlobals)

theorem htrNewPayload_call_normal_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word out)])
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_new_payload_request") arguments) = (none,post)) :
    post.globals = state.globals := by
  have frame := normalRel_apply (htrNewPayload_call_heapGlobals arguments)
    (X := state) (by rw [run]; exact Or.inl rfl) code
  rw [run] at frame
  have restored := htrNewPayload_call_normal_heap state post arguments pointer out heap args code atHeap run
  apply HolFiniteMapExact.ext
  funext name
  by_cases same : name = ofString "heap_ptr"
  · subst name
    exact restored.trans atHeap.symm
  · exact frame name same

#print axioms htrNewPayload_normal_heapGlobals
#print axioms htrNewPayload_call_heapGlobals
#print axioms htrNewPayload_call_normal_globals
end InitECandidate.Runtime
