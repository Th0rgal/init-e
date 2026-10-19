import InitECandidate.Runtime.MerkleHeapGlobals
import InitECandidate.Runtime.PackBytesReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Packing may advance the heap frontier, but retains every other global on
all continuing outcomes, including the actual returned structure. -/
theorem packBytes_normal_heapGlobals : NormalRel HeapGlobalsRel (sourceFunctionBody Guest.guestFn_pack_bytes) := by
  have pre := heapGlobalsRel_preorder
  rw [sourceFunctionBody_eq_structural]
  repeat first
    | exact normalRel_of_frame pre (originalGlobalsFrame_leaf _ (by intro watched; rfl))
    | apply normalRel_seq pre
    | apply normalRel_dec pre
    | apply normalRel_decCall pre _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup alloc_returned_heapGlobals
    | exact normalRel_of_frame pre (memcpy_call_globals_frame _)
    | exact normalRel_of_frame pre (memzero_call_globals_frame _)

#print axioms packBytes_normal_heapGlobals
end InitECandidate.Runtime
