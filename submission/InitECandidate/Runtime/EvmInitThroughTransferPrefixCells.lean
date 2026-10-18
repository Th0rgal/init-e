import InitECandidate.Runtime.EvmInitThroughTransferPrefix
import InitECandidate.Runtime.AlignedCellDomains
import InitECandidate.Runtime.MemzeroAlignedCallCells
import InitECandidate.Runtime.KeccakShortCallBoundCells
import InitECandidate.Runtime.EvmInitTransferPrefixCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem evaluate_evmInit_through_transfer_prefix_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer oldTopic : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (topicSlot : state.globals.lookup (ofString "transfer_topic") = some (.val (.word oldTopic)))
    (stateGlobal : state.globals.lookup (ofString "keccak_st") = some (.val (.word 2713714976)))
    (padGlobal : state.globals.lookup (ofString "keccak_pad") = some (.val (.word 2713715176)))
    (aligned : pointer.toNat % 8 = 0) (above : 2713714688 ≤ pointer.toNat)
    (small : pointer.toNat + 40 ≤ 33806089496)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → 2713714688 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (budget : 396 ≤ state.clock) :
    Reaches state (evmInitAt 0) (EvmThroughTransferReady state pointer) 396 (evmInitAt 38) := by
  have firstRun := evaluate_evmInit_temporary_released state pointer code heap aligned small (by omega)
  rcases firstRun with ⟨middle,ready,spent,remaining,agreement⟩ | aborted
  · have middleHeap : middle.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)) := by
      rw [ready.1]; exact heap
    have middleTopic : middle.globals.lookup (ofString "transfer_topic") = some (.val (.word oldTopic)) := by
      rw [ready.1]; exact topicSlot
    have middleState : middle.globals.lookup (ofString "keccak_st") = some (.val (.word 2713714976)) := by
      rw [ready.1]; exact stateGlobal
    have middlePad : middle.globals.lookup (ofString "keccak_pad") = some (.val (.word 2713715176)) := by
      rw [ready.1]; exact padGlobal
    have transfer := evaluate_evmInit_transfer_prefix_cells middle pointer oldTopic (ready.2.1.trans code)
      middleHeap ready.2.2.2 middleTopic middleState middlePad aligned above (by omega)
      (by intro address cellAligned lower upper; rw [ready.2.2.1]; exact arena address cellAligned lower upper) (by omega)
    have adapted : Reaches middle (evmInitAt 36) (EvmThroughTransferReady state pointer) 393 (evmInitAt 38) :=
      reaches_mono middle (evmInitAt 36) (evmInitAt 38) (EvmTransferReady middle pointer)
        (EvmThroughTransferReady state pointer) 393 393 (by omega)
        (by
          intro next valid
          refine ⟨?_,valid.2.1.trans ready.2.1,valid.2.2.1.trans ready.2.2.1,?_⟩
          · rw [valid.1,ready.1]
          · rw [valid.2.2.2]; exact ready.2.2.2)
        transfer
    exact reaches_trans state (evmInitAt 0) (evmInitAt 36) (evmInitAt 38)
      (fun next => next = middle) (EvmThroughTransferReady state pointer) 3 393
      (Or.inl ⟨middle,rfl,spent,remaining,agreement⟩)
      (by intro next equal; subst next; exact adapted)
  · exact Or.inr (stAbort_mono state _ 3 396 (by omega) aborted)

#print axioms evaluate_evmInit_through_transfer_prefix_cells
end InitECandidate.Runtime
