import InitECandidate.Runtime.EvmInitBodyReturned
import InitECandidate.Runtime.AlignedCellDomains
import InitECandidate.Runtime.MemzeroAlignedCallCells
import InitECandidate.Runtime.KeccakShortCallBoundCells
import InitECandidate.Runtime.EvmInitThroughTransferPrefixCells
import InitECandidate.Runtime.EvmInitAddressSuffixReturnedCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem evaluate_evmInit_body_returned_globals_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer oldTopic oldSystem oldNull oldEmpty oldKey oldHeader : BitVec 64) (value : ValueHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (topicSlot : state.globals.lookup (ofString "transfer_topic") = some (.val (.word oldTopic)))
    (systemSlot : state.globals.lookup (ofString "vm_system_address") = some (.val (.word oldSystem)))
    (nullSlot : state.globals.lookup (ofString "null_address") = some (.val (.word oldNull)))
    (emptySlot : state.globals.lookup (ofString "evm_empty") = some (.val (.word oldEmpty)))
    (keySlot : state.globals.lookup (ofString "evm_key_buf") = some (.val (.word oldKey)))
    (headerSlot : state.globals.lookup (ofString "pre_hdr_buf") = some (.val (.word oldHeader)))
    (stateGlobal : state.globals.lookup (ofString "keccak_st") = some (.val (.word 2713714976)))
    (padGlobal : state.globals.lookup (ofString "keccak_pad") = some (.val (.word 2713715176)))
    (aligned : pointer.toNat % 8 = 0) (above : 2713714688 ≤ pointer.toNat)
    (small : pointer.toNat + 216 ≤ 33806089496)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → 2713714688 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (budget : 457 ≤ state.clock)
    (returned : (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_evm_init)).1 = some (.returned value)) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_evm_init)).2.globals =
      globalAllocationGlobals state.globals pointer evmInitAllocations ∧
    ∃ finalHeap : BitVec 64,
      (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_evm_init)).2.globals.lookup (ofString "heap_ptr") =
        some (.val (.word finalHeap)) ∧ finalHeap.toNat = pointer.toNat + 216 := by
  have prefixRun := evaluate_evmInit_through_transfer_prefix_cells state pointer oldTopic code heap topicSlot
    stateGlobal padGlobal aligned above (by omega) arena (by omega)
  obtain ⟨next,ready,spent,_,agreement,normal⟩ :=
    reaches_returned_continuation state (evmInitAt 0) (evmInitAt 38) (EvmThroughTransferReady state pointer)
      396 value prefixRun returned
  have pointerNat : (allocationEnd pointer 32).toNat = pointer.toNat + 32 :=
    allocationEnd_aligned_toNat pointer 32 (by change pointer.toNat + 32 ≤ 33806089496; omega) aligned (by decide)
  have heapNext : next.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 32))) := by
    rw [ready.1]
    simp [evmTransferAllocation,globalAllocationGlobals,HolFiniteMapExact.lookup_update,FUPDATE,ofString]
  have systemNext : next.globals.lookup (ofString "vm_system_address") = some (.val (.word oldSystem)) := by
    rw [ready.1]
    simpa [evmTransferAllocation,globalAllocationGlobals,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using systemSlot
  have nullNext : next.globals.lookup (ofString "null_address") = some (.val (.word oldNull)) := by
    rw [ready.1]
    simpa [evmTransferAllocation,globalAllocationGlobals,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using nullSlot
  have emptyNext : next.globals.lookup (ofString "evm_empty") = some (.val (.word oldEmpty)) := by
    rw [ready.1]
    simpa [evmTransferAllocation,globalAllocationGlobals,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using emptySlot
  have keyNext : next.globals.lookup (ofString "evm_key_buf") = some (.val (.word oldKey)) := by
    rw [ready.1]
    simpa [evmTransferAllocation,globalAllocationGlobals,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using keySlot
  have headerNext : next.globals.lookup (ofString "pre_hdr_buf") = some (.val (.word oldHeader)) := by
    rw [ready.1]
    simpa [evmTransferAllocation,globalAllocationGlobals,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using headerSlot
  obtain ⟨tailGlobals,finalHeap,heapEnd,heapNat⟩ := evaluate_evmInit_address_suffix_returned_globals_cells next
    (allocationEnd pointer 32) oldSystem oldNull oldEmpty oldKey oldHeader value
    (ready.2.1.trans code) heapNext systemNext nullNext emptyNext keyNext headerNext
    (by rw [pointerNat]; omega) (by rw [pointerNat]; omega) (by rw [pointerNat]; omega)
    (by intro address cellAligned lower upper; rw [ready.2.2.1]; exact arena address cellAligned lower upper) (by omega) normal
  refine ⟨?_,finalHeap,?_,?_⟩
  · change (evaluateHOLFiniteState state (evmInitAt 0)).2.globals = _
    rw [agreement.2.2.2.1,tailGlobals,ready.1]
    simp only [evmInitAllocations,evmTransferAllocation,List.singleton_append,globalAllocationGlobals]
  · change (evaluateHOLFiniteState state (evmInitAt 0)).2.globals.lookup _ = _
    rw [agreement.2.2.2.1]
    exact heapEnd
  · rw [pointerNat] at heapNat
    omega

#print axioms evaluate_evmInit_body_returned_globals_cells
end InitECandidate.Runtime
