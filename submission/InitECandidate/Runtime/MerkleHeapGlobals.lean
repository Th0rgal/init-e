import InitECandidate.Runtime.HtabHeapFrame
import InitECandidate.Runtime.MerkleizeReturnedHeap
import InitECandidate.Runtime.Sha256GlobalsFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def HeapGlobalsRel (before after : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∀ name, name ≠ ofString "heap_ptr" → after.lookup name = before.lookup name

theorem heapGlobalsRel_preorder : GlobalsPreorder HeapGlobalsRel where
  refl := fun _ _ _ => rfl
  trans := fun _ _ _ a b name different => (b name different).trans (a name different)

theorem normalRel_heapGlobals_leaf (program : ProgHOL 64)
    (supported : ∀ name, name ≠ ofString "heap_ptr" → avoidsGlobalAssignment name program = true) :
    NormalRel HeapGlobalsRel program := by
  unfold NormalRel
  intro F state post result _ run _ name different
  have kept := evaluate_avoidsGlobalAssignment name program (supported name different) state
  rw [run] at kept
  exact kept

theorem alloc_returned_heapGlobals : ReturnedRel HeapGlobalsRel (sourceFunctionBody Guest.guestFn_alloc) := by
  unfold ReturnedRel at *
  intro F state post value code run
  have allocation := alloc_returnedRel
  unfold ReturnedRel at allocation
  exact (allocation state post value code run).1

theorem heapRelease_returned_heapGlobals : ReturnedRel HeapGlobalsRel (sourceFunctionBody Guest.guestFn_heap_release) := by
  apply NormalRel.returned
  apply normalRel_heapGlobals_leaf
  intro name different
  rw [source_heapRelease_body]
  simp [avoidsGlobalAssignment,Ne.symm different]

/-- Allocation and release can change the frontier while every other global
keeps its caller binding throughout all continuing original Merkle outcomes. -/
theorem merkleize_normal_heapGlobals : NormalRel HeapGlobalsRel (sourceFunctionBody Guest.guestFn_merkleize) := by
  have pre := heapGlobalsRel_preorder
  rw [sourceFunctionBody_eq_structural]
  repeat first
    | exact normalRel_of_frame pre (originalGlobalsFrame_leaf _ (by intro watched; rfl))
    | apply normalRel_seq pre
    | apply normalRel_dec pre
    | apply normalRel_ite pre
    | apply normalRel_while pre
    | apply normalRel_decCall pre _ _ _ _ _ _ _ originalRuntimeCode_ceilLog2_lookup
        (NormalRel.returned (normalRel_readOnly pre ceilLog2_readOnly))
    | apply normalRel_decCall pre _ _ _ _ _ _ _ vmLookup_max
        (NormalRel.returned (normalRel_readOnly pre max_readOnly))
    | apply normalRel_decCall pre _ _ _ _ _ _ _ vmLookup_heap_mark
        (NormalRel.returned (normalRel_readOnly pre heapMark_readOnly))
    | apply normalRel_decCall pre _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup alloc_returned_heapGlobals
    | exact normalRel_of_frame pre (memcpy_call_globals_frame _)
    | exact normalRel_of_frame pre (memzero_call_globals_frame _)
    | exact normalRel_of_frame pre (shaPair_call_globals_frame _)
    | exact normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_heap_release_lookup heapRelease_returned_heapGlobals

theorem merkleize_call_heapGlobals (arguments : List (ExpHOL 64)) :
    NormalRel HeapGlobalsRel (.call (some (none,none)) (ofString "merkleize") arguments) :=
  normalRel_discard_call heapGlobalsRel_preorder _ _ _ _ _ originalRuntimeCode_merkleize_lookup
    (NormalRel.returned merkleize_normal_heapGlobals)

/-- Normally returned original Merkle calls restore the whole caller global
map. This is partial correctness and requires no size, clock or read domain. -/
theorem merkleize_call_normal_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (p n limit out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word p),.val (.word n),.val (.word limit),.val (.word out)])
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "merkleize") arguments) = (none,post)) :
    post.globals = state.globals := by
  have frame := normalRel_apply (merkleize_call_heapGlobals arguments)
    (X := state) (by rw [run]; exact Or.inl rfl) code
  rw [run] at frame
  have restored := merkleize_call_normal_heap state post arguments p n limit out heap args code atHeap run
  apply HolFiniteMapExact.ext
  funext name
  by_cases same : name = ofString "heap_ptr"
  · subst name
    exact restored.trans atHeap.symm
  · exact frame name same

#print axioms heapGlobalsRel_preorder
#print axioms normalRel_heapGlobals_leaf
#print axioms alloc_returned_heapGlobals
#print axioms heapRelease_returned_heapGlobals
#print axioms merkleize_normal_heapGlobals
#print axioms merkleize_call_heapGlobals
#print axioms merkleize_call_normal_globals
end InitECandidate.Runtime
