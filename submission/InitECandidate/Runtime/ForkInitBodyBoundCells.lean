import InitECandidate.Runtime.ForkInitBodyBound
import InitECandidate.Runtime.AlignedCellDomains
import InitECandidate.Runtime.MemzeroAlignedCallCells
import InitECandidate.Runtime.KeccakShortCallBoundCells
import InitECandidate.Runtime.GlobalAllocationZeroPrefixCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem evaluate_forkInit_body_bounded_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer oldZero oldPrecompile : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (zeroSlot : state.globals.lookup (ofString "zero32") = some (.val (.word oldZero)))
    (precompileSlot : state.globals.lookup (ofString "precompile_addrs") = some (.val (.word oldPrecompile)))
    (aligned : pointer.toNat % 8 = 0)
    (small : pointer.toNat + 392 ≤ 33806089496)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → pointer.toNat ≤ address.toNat →
      address.toNat < pointer.toNat + 392 → state.memaddrs address)
    (budget : 515 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_fork_init)
    state.clock ≤ evaluated.2.clock + 515 ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  have safeZero : AllocationPlanSafe pointer [32] :=
    (allocationPlan_safe_aligned [32] pointer aligned
      (by intro size member; simp only [List.mem_singleton] at member; subst size; decide)
      (by change pointer.toNat + (32 + 0) ≤ 33806089496; omega)).1
  obtain ⟨middle,firstRun,firstCost,firstRemaining,firstCode,firstDomain,_,firstGlobals,_⟩ :=
    evaluate_globalAllocation_zero_prefix_cells state (ofString "zero32") pointer 32 oldZero (forkInitAt 2)
      code heap zeroSlot (by decide) safeZero aligned (by change pointer.toNat + 32 ≤ 33806089496; omega)
      (by intro address cellAligned lower upper; apply arena address cellAligned lower; change address.toNat < pointer.toNat + 32 at upper; omega)
      (by change 34 ≤ state.clock; omega)
  have middlePointer : (allocationEnd pointer 32).toNat = pointer.toNat + 32 := by
    exact allocationEnd_aligned_toNat pointer 32 (by change pointer.toNat + 32 ≤ 33806089496; omega) aligned (by decide)
  have middleAligned : (allocationEnd pointer 32).toNat % 8 = 0 := by
    rw [middlePointer]
    omega
  have middleHeap : middle.globals.lookup (ofString "heap_ptr") =
      some (.val (.word (allocationEnd pointer 32))) := by
    rw [firstGlobals]
    simp [globalAllocationGlobals,HolFiniteMapExact.lookup_update,FUPDATE,ofString]
  have middleSlot : middle.globals.lookup (ofString "precompile_addrs") =
      some (.val (.word oldPrecompile)) := by
    rw [firstGlobals]
    simpa [globalAllocationGlobals,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using precompileSlot
  have safePrecompile : AllocationPlanSafe (allocationEnd pointer 32) [360] :=
    (allocationPlan_safe_aligned [360] (allocationEnd pointer 32) middleAligned
      (by intro size member; simp only [List.mem_singleton] at member; subst size; decide)
      (by rw [middlePointer]; change pointer.toNat + 32 + (360 + 0) ≤ 33806089496; omega)).1
  have firstSpent : state.clock ≤ middle.clock + 34 := firstCost
  obtain ⟨next,secondRun,secondCost,secondRemaining,secondCode,_,_,_,_⟩ :=
    evaluate_globalAllocation_zero_prefix_cells middle (ofString "precompile_addrs") (allocationEnd pointer 32)
      360 oldPrecompile (forkInitAt 4) (firstCode.trans code) middleHeap middleSlot (by decide)
      safePrecompile middleAligned (by rw [middlePointer]; change pointer.toNat + 32 + 360 ≤ 33806089496; omega)
      (by
        intro address cellAligned lower upper
        rw [firstDomain]
        apply arena address cellAligned
        · rw [middlePointer] at lower; omega
        · rw [middlePointer] at upper; change address.toNat < pointer.toNat + 32 + 360 at upper; omega)
      (by change 362 ≤ middle.clock; omega)
  have secondSpent : middle.clock ≤ next.clock + 362 := secondCost
  have tail := evaluate_forkInit_counter_suffix_bounded next
    (secondCode.trans (firstCode.trans code)) (by omega)
  have actualRun : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_fork_init) =
      evaluateHOLFiniteState next (forkInitAt 4) := by
    change evaluateHOLFiniteState state (forkInitAt 0) = _
    rw [source_forkInit_zero32]
    change evaluateHOLFiniteState state (globalAllocationProgram _ _) = _
    rw [firstRun,evaluate_forkInit_precompile_normalized]
    exact secondRun
  change state.clock ≤ (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_fork_init)).2.clock + 515 ∧
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_fork_init)).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_fork_init)).1 ≠ some .timeOut
  rw [actualRun]
  exact ⟨by omega,by omega,tail.2.2⟩

#print axioms evaluate_forkInit_body_bounded_cells
end InitECandidate.Runtime
