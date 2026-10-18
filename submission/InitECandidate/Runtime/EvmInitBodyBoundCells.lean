import InitECandidate.Runtime.EvmInitBodyBound
import InitECandidate.Runtime.AlignedCellDomains
import InitECandidate.Runtime.MemzeroAlignedCallCells
import InitECandidate.Runtime.KeccakShortCallBoundCells
import InitECandidate.Runtime.EvmInitThroughTransferPrefixCells
import InitECandidate.Runtime.EvmInitAddressSuffixBoundCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem evaluate_evmInit_body_bounded_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer oldTopic oldSystem oldNull oldEmpty : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (topicSlot : state.globals.lookup (ofString "transfer_topic") = some (.val (.word oldTopic)))
    (systemSlot : state.globals.lookup (ofString "vm_system_address") = some (.val (.word oldSystem)))
    (nullSlot : state.globals.lookup (ofString "null_address") = some (.val (.word oldNull)))
    (emptySlot : state.globals.lookup (ofString "evm_empty") = some (.val (.word oldEmpty)))
    (stateGlobal : state.globals.lookup (ofString "keccak_st") = some (.val (.word 2713714976)))
    (padGlobal : state.globals.lookup (ofString "keccak_pad") = some (.val (.word 2713715176)))
    (aligned : pointer.toNat % 8 = 0) (above : 2713714688 ≤ pointer.toNat)
    (small : pointer.toNat + 88 ≤ 33806089496)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → 2713714688 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (budget : 457 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_evm_init)
    state.clock ≤ evaluated.2.clock + 457 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have prefixRun := evaluate_evmInit_through_transfer_prefix_cells state pointer oldTopic code heap topicSlot
    stateGlobal padGlobal aligned above (by omega) arena (by omega)
  change state.clock ≤ (evaluateHOLFiniteState state (evmInitAt 0)).2.clock + 457 ∧
    (evaluateHOLFiniteState state (evmInitAt 0)).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState state (evmInitAt 0)).1 ≠ some .timeOut
  apply evaluate_reaches_terminal_bounded state (evmInitAt 0) (evmInitAt 38)
    (EvmThroughTransferReady state pointer) 396 61 budget prefixRun
  intro next ready fuel
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
  exact evaluate_evmInit_address_suffix_bounded_cells next (allocationEnd pointer 32) oldSystem oldNull oldEmpty
    (ready.2.1.trans code) heapNext systemNext nullNext emptyNext
    (by rw [pointerNat]; omega) (by rw [pointerNat]; omega) (by rw [pointerNat]; omega)
    (by intro address cellAligned lower upper; rw [ready.2.2.1]; exact arena address cellAligned lower upper) fuel

#print axioms evaluate_evmInit_body_bounded_cells
end InitECandidate.Runtime
