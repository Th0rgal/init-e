import InitECandidate.Runtime.ProgressiveHeapGlobals
import InitECandidate.Runtime.PackBytesHeapGlobals
import InitECandidate.Runtime.MixInLengthGlobalsFrame
import InitECandidate.Runtime.HtrPbytesCallBound
import InitECandidate.Runtime.HtrBytesListCallBound
import InitECandidate.Runtime.HtrBytesVectorCallBound
import InitECandidate.Runtime.HtrPlistChunksCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem htrPlistChunks_normal_heapGlobals : NormalRel HeapGlobalsRel (sourceFunctionBody Guest.guestFn_htr_plist_chunks) := by
  have pre := heapGlobalsRel_preorder
  rw [sourceFunctionBody_eq_structural]
  repeat first
    | exact normalRel_of_frame pre (originalGlobalsFrame_leaf _ (by intro watched; rfl))
    | apply normalRel_seq pre
    | exact progressive_call_heapGlobals _
    | exact normalRel_of_frame pre (mixInLength_call_globals_frame _)

theorem htrPlistChunks_call_heapGlobals (arguments : List (ExpHOL 64)) :
    NormalRel HeapGlobalsRel (.call (some (none,none)) (ofString "htr_plist_chunks") arguments) :=
  normalRel_discard_call heapGlobalsRel_preorder _ _ _ _ _ originalRuntimeCode_htr_plist_chunks_lookup
    (NormalRel.returned htrPlistChunks_normal_heapGlobals)

/-- Every continuing packing/hash/release path preserves the caller's
non-heap globals. Heap restoration is a separate returned-path obligation. -/
theorem htrPbytes_normal_heapGlobals : NormalRel HeapGlobalsRel (sourceFunctionBody Guest.guestFn_htr_pbytes) := by
  have pre := heapGlobalsRel_preorder
  rw [sourceFunctionBody_eq_structural]
  repeat first
    | exact normalRel_of_frame pre (originalGlobalsFrame_leaf _ (by intro watched; rfl))
    | apply normalRel_seq pre
    | apply normalRel_decCall pre _ _ _ _ _ _ _ vmLookup_heap_mark
        (NormalRel.returned (normalRel_readOnly pre heapMark_readOnly))
    | apply normalRel_decCall pre _ _ _ _ _ _ _ originalRuntimeCode_packBytes_lookup
        (NormalRel.returned packBytes_normal_heapGlobals)
    | exact htrPlistChunks_call_heapGlobals _
    | exact normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_heap_release_lookup heapRelease_returned_heapGlobals

theorem htrBytesList_normal_heapGlobals : NormalRel HeapGlobalsRel (sourceFunctionBody Guest.guestFn_htr_bytes_list) := by
  have pre := heapGlobalsRel_preorder
  rw [sourceFunctionBody_eq_structural]
  repeat first
    | exact normalRel_of_frame pre (originalGlobalsFrame_leaf _ (by intro watched; rfl))
    | apply normalRel_seq pre
    | apply normalRel_decCall pre _ _ _ _ _ _ _ vmLookup_heap_mark
        (NormalRel.returned (normalRel_readOnly pre heapMark_readOnly))
    | apply normalRel_decCall pre _ _ _ _ _ _ _ originalRuntimeCode_packBytes_lookup
        (NormalRel.returned packBytes_normal_heapGlobals)
    | exact merkleize_call_heapGlobals _
    | exact normalRel_of_frame pre (mixInLength_call_globals_frame _)
    | exact normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_heap_release_lookup heapRelease_returned_heapGlobals

theorem htrBytesVector_normal_heapGlobals : NormalRel HeapGlobalsRel (sourceFunctionBody Guest.guestFn_htr_bytes_vector) := by
  have pre := heapGlobalsRel_preorder
  rw [sourceFunctionBody_eq_structural]
  repeat first
    | exact normalRel_of_frame pre (originalGlobalsFrame_leaf _ (by intro watched; rfl))
    | apply normalRel_seq pre
    | apply normalRel_ite pre
    | apply normalRel_decCall pre _ _ _ _ _ _ _ vmLookup_heap_mark
        (NormalRel.returned (normalRel_readOnly pre heapMark_readOnly))
    | apply normalRel_decCall pre _ _ _ _ _ _ _ originalRuntimeCode_packBytes_lookup
        (NormalRel.returned packBytes_normal_heapGlobals)
    | exact merkleize_call_heapGlobals _
    | exact normalRel_of_frame pre (memcpy_call_globals_frame _)
    | exact normalRel_of_frame pre (memzero_call_globals_frame _)
    | exact normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_heap_release_lookup heapRelease_returned_heapGlobals

#print axioms htrPlistChunks_normal_heapGlobals
#print axioms htrPlistChunks_call_heapGlobals
#print axioms htrPbytes_normal_heapGlobals
#print axioms htrBytesList_normal_heapGlobals
#print axioms htrBytesVector_normal_heapGlobals
end InitECandidate.Runtime
