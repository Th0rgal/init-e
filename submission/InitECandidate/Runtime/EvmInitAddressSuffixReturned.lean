import InitECandidate.Runtime.EvmInitAddressSuffixBound
import InitECandidate.Runtime.EvmInitCounterSuffixReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def evmAddressSuffixAllocations : List (MlS × BitVec 64) :=
  evmSystemAddressAllocation ++ evmZeroSuffixAllocations

/-- Normal return from the system-address suffix exposes the exact five
allocation globals and advances its incoming heap by 184 bytes. -/
theorem evaluate_evmInit_address_suffix_returned_globals {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer oldSystem oldNull oldEmpty oldKey oldHeader : BitVec 64) (value : ValueHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (systemSlot : state.globals.lookup (ofString "vm_system_address") = some (.val (.word oldSystem)))
    (nullSlot : state.globals.lookup (ofString "null_address") = some (.val (.word oldNull)))
    (emptySlot : state.globals.lookup (ofString "evm_empty") = some (.val (.word oldEmpty)))
    (keySlot : state.globals.lookup (ofString "evm_key_buf") = some (.val (.word oldKey)))
    (headerSlot : state.globals.lookup (ofString "pre_hdr_buf") = some (.val (.word oldHeader)))
    (aligned : pointer.toNat % 8 = 0) (above : 2713714688 ≤ pointer.toNat)
    (small : pointer.toNat + 184 ≤ 33806089496)
    (arena : ∀ address : BitVec 64, 2713714688 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (budget : 61 ≤ state.clock)
    (returned : (evaluateHOLFiniteState state (evmInitAt 38)).1 = some (.returned value)) :
    (evaluateHOLFiniteState state (evmInitAt 38)).2.globals =
      globalAllocationGlobals state.globals pointer evmAddressSuffixAllocations ∧
    ∃ finalHeap : BitVec 64,
      (evaluateHOLFiniteState state (evmInitAt 38)).2.globals.lookup (ofString "heap_ptr") =
        some (.val (.word finalHeap)) ∧ finalHeap.toNat = pointer.toNat + 184 := by
  have safe : AllocationPlanSafe pointer [24] :=
    (allocationPlan_safe_aligned [24] pointer aligned
      (by intro size member; simp only [List.mem_singleton] at member; subst size; decide)
      (by change pointer.toNat + (24 + 0) ≤ 33806089496; omega)).1
  obtain ⟨next,run,clock,_,_,installed,domain,globals,heapEnd⟩ :=
    evaluate_globalAllocation_prefix state evmSystemAddressAllocation (evmInitAt 39) pointer code heap
      (by intro entry member; simp only [evmSystemAddressAllocation,List.mem_singleton] at member; subst entry; decide)
      (by intro entry member; simp only [evmSystemAddressAllocation,List.mem_singleton] at member; subst entry; exact ⟨oldSystem,systemSlot⟩)
      safe (by change 1 ≤ state.clock; omega)
  have clockEq : next.clock = state.clock - 1 := clock
  have pointerNat : (allocationEnd pointer 24).toNat = pointer.toNat + 24 :=
    allocationEnd_aligned_toNat pointer 24 (by change pointer.toNat + 24 ≤ 33806089496; omega) aligned (by decide)
  have heapNext : next.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 24))) := heapEnd
  have nullNext : next.globals.lookup (ofString "null_address") = some (.val (.word oldNull)) := by
    rw [globals]
    simpa [evmSystemAddressAllocation,globalAllocationGlobals,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using nullSlot
  have emptyNext : next.globals.lookup (ofString "evm_empty") = some (.val (.word oldEmpty)) := by
    rw [globals]
    simpa [evmSystemAddressAllocation,globalAllocationGlobals,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using emptySlot
  have keyNext : next.globals.lookup (ofString "evm_key_buf") = some (.val (.word oldKey)) := by
    rw [globals]
    simpa [evmSystemAddressAllocation,globalAllocationGlobals,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using keySlot
  have headerNext : next.globals.lookup (ofString "pre_hdr_buf") = some (.val (.word oldHeader)) := by
    rw [globals]
    simpa [evmSystemAddressAllocation,globalAllocationGlobals,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using headerSlot
  have actualRun : evaluateHOLFiniteState state (evmInitAt 38) = evaluateHOLFiniteState next (evmInitAt 39) := by
    rw [source_evmInit_system_address_allocation]
    exact run
  have normal : (evaluateHOLFiniteState next (evmInitAt 39)).1 = some (.returned value) :=
    (congrArg Prod.fst actualRun).symm.trans returned
  obtain ⟨tailGlobals,finalHeap,heapLast,heapNat⟩ := evaluate_evmInit_counter_suffix_returned_globals next
    (allocationEnd pointer 24) oldNull oldEmpty oldKey oldHeader value
    (installed.trans code) heapNext nullNext emptyNext keyNext headerNext
    (by rw [pointerNat]; omega) (by rw [pointerNat]; omega)
    (by
      intro address lower upper
      rw [domain]
      apply arena address
      · rw [pointerNat] at lower; omega
      · rw [pointerNat] at upper; omega)
    (by omega) normal
  refine ⟨?_,finalHeap,?_,?_⟩
  · rw [actualRun,tailGlobals,globals]
    simp only [evmAddressSuffixAllocations,evmSystemAddressAllocation,List.singleton_append,globalAllocationGlobals]
  · rw [actualRun]
    exact heapLast
  · rw [pointerNat] at heapNat
    omega

#print axioms evaluate_evmInit_address_suffix_returned_globals
end InitECandidate.Runtime
