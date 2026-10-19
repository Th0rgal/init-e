import InitECandidate.Runtime.HtrHeapGlobals
import InitECandidate.Runtime.HtrRequestsReturnedHeap
import InitECandidate.Runtime.HtrPcontainerGlobals
import InitECandidate.Runtime.HtrRequestListGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem htrRequests_normal_heapGlobals : NormalRel HeapGlobalsRel (sourceFunctionBody Guest.guestFn_htr_requests) := by
  have pre := heapGlobalsRel_preorder
  rw [sourceFunctionBody_eq_structural]
  repeat first
    | exact normalRel_of_frame pre (originalGlobalsFrame_leaf _ (by intro watched; rfl))
    | apply normalRel_seq pre
    | apply normalRel_decCall pre _ _ _ _ _ _ _ vmLookup_heap_mark
        (NormalRel.returned (normalRel_readOnly pre heapMark_readOnly))
    | apply normalRel_decCall pre _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup alloc_returned_heapGlobals
    | exact htrRequestList_call_heapGlobals _
    | exact htrPcontainer_call_heapGlobals _
    | exact normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_heap_release_lookup heapRelease_returned_heapGlobals

theorem htrRequests_call_heapGlobals (arguments : List (ExpHOL 64)) :
    NormalRel HeapGlobalsRel (.call (some (none,none)) (ofString "htr_requests") arguments) :=
  normalRel_discard_call heapGlobalsRel_preorder _ _ _ _ _ originalRuntimeCode_htrRequests_lookup
    (NormalRel.returned htrRequests_normal_heapGlobals)

theorem htrRequests_call_normal_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word out)])
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_requests") arguments) = (none,post)) :
    post.globals = state.globals := by
  have frame := normalRel_apply (htrRequests_call_heapGlobals arguments)
    (X := state) (by rw [run]; exact Or.inl rfl) code
  rw [run] at frame
  have restored := htrRequests_call_normal_heap state post arguments pointer out heap args code atHeap run
  apply HolFiniteMapExact.ext
  funext name
  by_cases same : name = ofString "heap_ptr"
  · subst name
    exact restored.trans atHeap.symm
  · exact frame name same

#print axioms htrRequests_normal_heapGlobals
#print axioms htrRequests_call_heapGlobals
#print axioms htrRequests_call_normal_globals
end InitECandidate.Runtime
