import InitECandidate.Runtime.MerkleHeapGlobals
import InitECandidate.Runtime.ProgressiveReturnedHeap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Allocation and release can change the frontier while every other global
keeps its caller binding throughout all continuing original progressive Merkle outcomes. -/
theorem progressive_normal_heapGlobals : NormalRel HeapGlobalsRel (sourceFunctionBody Guest.guestFn_merkleize_progressive) := by
  have pre := heapGlobalsRel_preorder
  rw [sourceFunctionBody_eq_structural]
  repeat first
    | exact normalRel_of_frame pre (originalGlobalsFrame_leaf _ (by intro watched; rfl))
    | apply normalRel_seq pre
    | apply normalRel_dec pre
    | apply normalRel_ite pre
    | apply normalRel_while pre
    | apply normalRel_decCall pre _ _ _ _ _ _ _ vmLookup_heap_mark
        (NormalRel.returned (normalRel_readOnly pre heapMark_readOnly))
    | apply normalRel_decCall pre _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup alloc_returned_heapGlobals
    | exact normalRel_of_frame pre (memcpy_call_globals_frame _)
    | exact normalRel_of_frame pre (memzero_call_globals_frame _)
    | exact normalRel_of_frame pre (shaPair_call_globals_frame _)
    | exact merkleize_call_heapGlobals _
    | exact normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_heap_release_lookup heapRelease_returned_heapGlobals

theorem progressive_call_heapGlobals (arguments : List (ExpHOL 64)) :
    NormalRel HeapGlobalsRel (.call (some (none,none)) (ofString "merkleize_progressive") arguments) :=
  normalRel_discard_call heapGlobalsRel_preorder _ _ _ _ _ originalRuntimeCode_progressive_lookup
    (NormalRel.returned progressive_normal_heapGlobals)

/-- Normally returned original progressive Merkle calls restore the whole caller global
map. This is partial correctness and requires no size, clock or read domain. -/
theorem progressive_call_normal_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (p n out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word p),.val (.word n),.val (.word out)])
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "merkleize_progressive") arguments) = (none,post)) :
    post.globals = state.globals := by
  have frame := normalRel_apply (progressive_call_heapGlobals arguments)
    (X := state) (by rw [run]; exact Or.inl rfl) code
  rw [run] at frame
  have restored := progressive_call_normal_heap state post arguments p n out heap args code atHeap run
  apply HolFiniteMapExact.ext
  funext name
  by_cases same : name = ofString "heap_ptr"
  · subst name
    exact restored.trans atHeap.symm
  · exact frame name same

#print axioms progressive_normal_heapGlobals
#print axioms progressive_call_heapGlobals
#print axioms progressive_call_normal_globals
end InitECandidate.Runtime
