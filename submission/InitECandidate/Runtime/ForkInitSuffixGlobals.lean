import InitECandidate.Runtime.AllocationFramedGlobals
import InitECandidate.Runtime.BigEndianGlobalsFrame
import InitECandidate.Runtime.ForkInitSuffixBound
import InitECandidate.Runtime.ByteStoresControlFrame
import InitECandidate.Runtime.DiscardCallNoReturn
import InitECandidate.Runtime.AllocationPlanAligned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def forkSuffixAllocations : List (MlS × BitVec 64) :=
  [(ofString "beacon_roots_address",24),(ofString "history_storage_address",24),
   (ofString "withdrawal_request_address",24),(ofString "consolidation_request_address",24),
   (ofString "builder_deposit_address",24),(ofString "builder_exit_address",24),
   (ofString "deposit_contract_address",24),(ofString "deposit_event_signature_hash",32)]

theorem evaluate_storeByte_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination value : ExpHOL 64) (output : ValueHOL 64) :
    (evaluateHOLFiniteState state (.storeByte destination value)).1 ≠ some (.returned output) := by
  have control := (evaluate_storeByte_control_frame state destination value).1
  rcases control with equal | equal <;> rw [equal] <;> simp

theorem forkInit_suffix_globals_fragment :
    AllocationFramedGlobals (forkInitStructuralAt 6) forkSuffixAllocations := by
  repeat first
    | exact AllocationFramedGlobals.finish
    | apply AllocationFramedGlobals.allocation
    | apply AllocationFramedGlobals.framed _ (addressFromWords_call_globals_frame _)
        (by intro F state value; exact evaluate_discard_call_no_return state _ _ value)
    | apply AllocationFramedGlobals.framed _ (storeBE64_call_globals_frame _)
        (by intro F state value; exact evaluate_discard_call_no_return state _ _ value)
    | apply AllocationFramedGlobals.framed _ (originalGlobalsFrame_leaf _ (fun _ => rfl))
        (by intro F state value; exact evaluate_storeByte_no_return state _ _ value)

/-- A returned fork suffix has the exact eight persistent allocation globals
and advances its incoming heap by 200 bytes. Serializer failure paths need
no additional success or memory assumptions. -/
theorem evaluate_forkInit_suffix_returned_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (value : ValueHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (words : ∀ entry ∈ forkSuffixAllocations, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (aligned : pointer.toNat % 8 = 0) (small : pointer.toNat + 200 ≤ 33806089496)
    (run : evaluateHOLFiniteState state (forkInitAt 6) = (some (.returned value),post)) :
    value = .val (.word 0) ∧ post.globals = globalAllocationGlobals state.globals pointer forkSuffixAllocations ∧
      ∃ finalHeap : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
        finalHeap.toNat = pointer.toNat + 200 := by
  have alignedSizes : ∀ size ∈ forkSuffixAllocations.map Prod.snd, size.toNat % 8 = 0 := by
    intro size member
    simp only [forkSuffixAllocations,List.map_cons,List.map_nil,Prod.snd,List.mem_cons,
      List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have plan := allocationPlan_safe_aligned (forkSuffixAllocations.map Prod.snd) pointer aligned alignedSizes
    (by simpa [forkSuffixAllocations] using small)
  have names : ∀ entry ∈ forkSuffixAllocations, entry.1 ≠ ofString "heap_ptr" := by decide
  have fragment : AllocationFramedGlobals (forkInitAt 6) forkSuffixAllocations := by
    rw [forkInitAt_eq_structural]
    exact forkInit_suffix_globals_fragment
  obtain ⟨zero,globals⟩ := fragment.returned state post pointer value code heap names words plan.1 run
  refine ⟨zero,globals,allocationPlanEnd pointer (forkSuffixAllocations.map Prod.snd),?_,?_⟩
  · rw [globals]
    exact globalAllocationGlobals_heap_frontier state.globals pointer forkSuffixAllocations heap names
  · simpa [forkSuffixAllocations] using plan.2

#print axioms evaluate_storeByte_no_return
#print axioms forkInit_suffix_globals_fragment
#print axioms evaluate_forkInit_suffix_returned_globals
end InitECandidate.Runtime
