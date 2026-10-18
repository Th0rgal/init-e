import InitECandidate.Runtime.EvmInitCounterSuffixReturned
import InitECandidate.Runtime.AlignedCellDomains
import InitECandidate.Runtime.MemzeroAlignedCallCells
import InitECandidate.Runtime.KeccakShortCallBoundCells
import InitECandidate.Runtime.EvmInitZeroSuffixSuccessCells
import InitECandidate.Runtime.EvmInitCounterSuffixBoundCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem evaluate_evmInit_counter_suffix_returned_globals_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer oldNull oldEmpty oldKey oldHeader : BitVec 64) (value : ValueHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (nullSlot : state.globals.lookup (ofString "null_address") = some (.val (.word oldNull)))
    (emptySlot : state.globals.lookup (ofString "evm_empty") = some (.val (.word oldEmpty)))
    (keySlot : state.globals.lookup (ofString "evm_key_buf") = some (.val (.word oldKey)))
    (headerSlot : state.globals.lookup (ofString "pre_hdr_buf") = some (.val (.word oldHeader)))
    (aligned : pointer.toNat % 8 = 0) (small : pointer.toNat + 160 ≤ 33806089496)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → pointer.toNat ≤ address.toNat →
      address.toNat < pointer.toNat + 32 → state.memaddrs address)
    (budget : 60 ≤ state.clock)
    (returned : (evaluateHOLFiniteState state (evmInitAt 39)).1 = some (.returned value)) :
    (evaluateHOLFiniteState state (evmInitAt 39)).2.globals =
      globalAllocationGlobals state.globals pointer evmZeroSuffixAllocations ∧
    ∃ finalHeap : BitVec 64,
      (evaluateHOLFiniteState state (evmInitAt 39)).2.globals.lookup (ofString "heap_ptr") =
        some (.val (.word finalHeap)) ∧ finalHeap.toNat = pointer.toNat + 160 := by
  obtain ⟨middle,loopFrame,loopSpent,_,loopAgreement,middleReturned⟩ :=
    reaches_returned_continuation state (evmInitAt 39) (evmInitAt 41) (InitializerCounterFinished state 20)
      20 value (evaluate_evmInit_counter_prefix state (by omega)) returned
  have byteReach : Reaches middle (evmInitAt 41) (ByteStoreControlFrame middle) 0 (evmInitAt 42) := by
    rw [source_evmInit_last_address_byte]
    exact evaluate_storeByte_reaches middle _ _ _
  obtain ⟨ready,byteFrame,byteSpent,_,byteAgreement,_⟩ :=
    reaches_returned_continuation middle (evmInitAt 41) (evmInitAt 42) (ByteStoreControlFrame middle)
      0 value byteReach middleReturned
  have readyGlobals : ready.globals = state.globals := byteFrame.1.trans loopFrame.1
  have readyCode : ready.code = state.code := byteFrame.2.2.1.trans loopFrame.2.1
  have readyDomain : ready.memaddrs = state.memaddrs := byteFrame.2.2.2.trans loopFrame.2.2.1
  obtain ⟨post,run,_,_,globals,_,_,_,finalHeap,heapEnd,heapNat⟩ :=
    evaluate_evmInit_zero_suffix_success_cells ready pointer oldNull oldEmpty oldKey oldHeader
      (readyCode.trans code) (by rw [readyGlobals]; exact heap)
      (by rw [readyGlobals]; exact nullSlot) (by rw [readyGlobals]; exact emptySlot)
      (by rw [readyGlobals]; exact keySlot) (by rw [readyGlobals]; exact headerSlot) aligned small
      (by intro address cellAligned lower upper; rw [readyDomain]; exact arena address cellAligned lower upper) (by omega)
  have actualGlobals : (evaluateHOLFiniteState state (evmInitAt 39)).2.globals = post.globals := by
    have same := loopAgreement.2.2.2.1.trans byteAgreement.2.2.2.1
    rw [run] at same
    exact same
  refine ⟨?_,finalHeap,?_,heapNat⟩
  · rw [actualGlobals,globals,readyGlobals]
  · rw [actualGlobals]
    exact heapEnd

#print axioms evaluate_evmInit_counter_suffix_returned_globals_cells
end InitECandidate.Runtime
