import InitECandidate.Runtime.EvmInitTransferPrefix
import InitECandidate.Runtime.AlignedCellDomains
import InitECandidate.Runtime.MemzeroAlignedCallCells
import InitECandidate.Runtime.KeccakShortCallBoundCells
import InitECandidate.Runtime.EvmInitTransferHashBoundCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem evaluate_evmInit_transfer_prefix_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer oldTopic : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (sourceLocal : state.locals.lookup (ofString "s") = some (.val (.word pointer)))
    (topicSlot : state.globals.lookup (ofString "transfer_topic") = some (.val (.word oldTopic)))
    (stateGlobal : state.globals.lookup (ofString "keccak_st") = some (.val (.word 2713714976)))
    (padGlobal : state.globals.lookup (ofString "keccak_pad") = some (.val (.word 2713715176)))
    (aligned : pointer.toNat % 8 = 0) (above : 2713714688 ≤ pointer.toNat)
    (small : pointer.toNat + 33 ≤ 33806089496)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → 2713714688 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (budget : 393 ≤ state.clock) :
    Reaches state (evmInitAt 36) (EvmTransferReady state pointer) 393 (evmInitAt 38) := by
  have safe : AllocationPlanSafe pointer [32] :=
    (allocationPlan_safe_aligned [32] pointer aligned
      (by intro size member; simp only [List.mem_singleton] at member; subst size; decide)
      (by change pointer.toNat + (32 + 0) ≤ 33806089496; omega)).1
  obtain ⟨allocated,allocationRun,allocationClock,_,allocationLocals,allocationCode,allocationDomain,allocationGlobals,_⟩ :=
    evaluate_globalAllocation_prefix state evmTransferAllocation (evmInitAt 37) pointer code heap
      (by intro entry member; simp only [evmTransferAllocation,List.mem_singleton] at member; subst entry; decide)
      (by intro entry member; simp only [evmTransferAllocation,List.mem_singleton] at member; subst entry; exact ⟨oldTopic,topicSlot⟩)
      safe (by change 1 ≤ state.clock; omega)
  have clock : allocated.clock = state.clock - 1 := allocationClock
  have atSource : allocated.locals.lookup (ofString "s") = some (.val (.word pointer)) := by
    rw [allocationLocals]; exact sourceLocal
  have atTopic : allocated.globals.lookup (ofString "transfer_topic") = some (.val (.word pointer)) := by
    rw [allocationGlobals]
    simp [evmTransferAllocation,globalAllocationGlobals,HolFiniteMapExact.lookup_update,FUPDATE]
  have atState : allocated.globals.lookup (ofString "keccak_st") = some (.val (.word 2713714976)) := by
    rw [allocationGlobals]
    simpa [evmTransferAllocation,globalAllocationGlobals,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using stateGlobal
  have atPad : allocated.globals.lookup (ofString "keccak_pad") = some (.val (.word 2713715176)) := by
    rw [allocationGlobals]
    simpa [evmTransferAllocation,globalAllocationGlobals,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using padGlobal
  have bounded := evaluate_evmInit_transfer_hash_bounded_cells allocated pointer pointer atSource atTopic atState atPad
    (allocationCode.trans code) (by omega) above small aligned aligned
    (by intro address cellAligned lower upper; rw [allocationDomain]; exact arena address cellAligned lower upper)
  have hashReach : Reaches allocated (evmInitAt 37) (EvmTransferReady state pointer) 392 (evmInitAt 38) := by
    rw [source_evmInit_transfer_hash]
    apply reaches_seq
    cases run : evaluateHOLFiniteState allocated
        (.call (some (none,none)) (ofString "keccak256") evmInitTransferHashArguments) with
    | mk result next =>
      rw [run] at bounded
      dsimp only at bounded
      obtain ⟨spent,remaining,noTimeout,globals,installed,domain,locals⟩ := bounded
      cases result with
      | none => exact Or.inl ⟨next,⟨globals.trans allocationGlobals,installed.trans allocationCode,
          domain.trans allocationDomain,(locals rfl).trans allocationLocals⟩,spent,remaining,rfl⟩
      | some result =>
        right
        refine ⟨result,rfl,?_,spent,remaining,?_⟩
        · intro value equal
          have consumed := evaluate_discard_call_no_return allocated (ofString "keccak256") evmInitTransferHashArguments value
          rw [run] at consumed
          exact consumed (by rw [equal])
        · intro _ equal
          exact noTimeout (by rw [equal])
  have prefixRun : Reaches state (evmInitAt 36) (fun next => next = allocated) 1 (evmInitAt 37) := by
    refine Or.inl ⟨allocated,rfl,by omega,by omega,?_⟩
    rw [source_evmInit_transfer_allocation,allocationRun]
    exact scoped_refl _
  exact reaches_trans state (evmInitAt 36) (evmInitAt 37) (evmInitAt 38)
    (fun next => next = allocated) (EvmTransferReady state pointer) 1 392 prefixRun
    (by intro next equal; subst next; exact hashReach)

#print axioms evaluate_evmInit_transfer_prefix_cells
end InitECandidate.Runtime
