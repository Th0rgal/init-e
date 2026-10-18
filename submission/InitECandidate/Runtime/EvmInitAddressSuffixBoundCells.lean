import InitECandidate.Runtime.EvmInitAddressSuffixBound
import InitECandidate.Runtime.AlignedCellDomains
import InitECandidate.Runtime.MemzeroAlignedCallCells
import InitECandidate.Runtime.KeccakShortCallBoundCells
import InitECandidate.Runtime.EvmInitCounterSuffixBoundCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem evaluate_evmInit_address_suffix_bounded_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer oldSystem oldNull oldEmpty : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (systemSlot : state.globals.lookup (ofString "vm_system_address") = some (.val (.word oldSystem)))
    (nullSlot : state.globals.lookup (ofString "null_address") = some (.val (.word oldNull)))
    (emptySlot : state.globals.lookup (ofString "evm_empty") = some (.val (.word oldEmpty)))
    (aligned : pointer.toNat % 8 = 0) (above : 2713714688 ≤ pointer.toNat)
    (small : pointer.toNat + 56 ≤ 33806089496)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → 2713714688 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (budget : 61 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (evmInitAt 38)
    state.clock ≤ evaluated.2.clock + 61 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
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
  have tail := evaluate_evmInit_counter_suffix_bounded_cells next (allocationEnd pointer 24) oldNull oldEmpty
    (installed.trans code) heapNext nullNext emptyNext
    (by rw [pointerNat]; omega) (by rw [pointerNat]; omega)
    (by
      intro address cellAligned lower upper
      rw [domain]
      apply arena address cellAligned
      · rw [pointerNat] at lower; omega
      · rw [pointerNat] at upper; omega)
    (by omega)
  change state.clock ≤ (evaluateHOLFiniteState state (evmInitAt 38)).2.clock + 61 ∧
    (evaluateHOLFiniteState state (evmInitAt 38)).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState state (evmInitAt 38)).1 ≠ some .timeOut
  rw [source_evmInit_system_address_allocation,run]
  exact ⟨by omega,by omega,tail.2.2⟩

#print axioms evaluate_evmInit_address_suffix_bounded_cells
end InitECandidate.Runtime
