import InitECandidate.Runtime.ForkInitAllocationSource
import InitECandidate.Runtime.ProgBounded
import InitECandidate.Runtime.AllocationPlanAligned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000

theorem source_evmInit_null_zero : evmInitAt 42 =
    globalAllocationZeroProgram (ofString "null_address") 24 (evmInitAt 44) := by
  simp only [evmInitAt,statelessNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_evmInit_empty_zero : evmInitAt 44 =
    globalAllocationZeroProgram (ofString "evm_empty") 8 (evmInitAt 46) := by
  simp only [evmInitAt,statelessNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_evmInit_final_allocations : evmInitAt 46 =
    globalAllocationProgram [(ofString "evm_key_buf",32),(ofString "pre_hdr_buf",96)] (.return (.const 0)) := by
  simp only [evmInitAt,statelessNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evmInit_final_allocations_bounded : ProgBounded (evmInitAt 46) 4 := by
  rw [source_evmInit_final_allocations]
  exact ProgBounded.seq (ProgBounded.alloc _ _)
    (ProgBounded.seq (ProgBounded.alloc _ _) (ProgBounded.straight _ (by rfl)))

/-- Zero both address buffers and evaluate the final allocator calls. Only
the first 32 bytes must be accessible; final allocator failures are covered. -/
theorem evaluate_evmInit_zero_suffix_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer oldNull oldEmpty : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (nullSlot : state.globals.lookup (ofString "null_address") = some (.val (.word oldNull)))
    (emptySlot : state.globals.lookup (ofString "evm_empty") = some (.val (.word oldEmpty)))
    (aligned : pointer.toNat % 8 = 0)
    (small : pointer.toNat + 32 ≤ 33806089496)
    (arena : ∀ address : BitVec 64, pointer.toNat ≤ address.toNat →
      address.toNat < pointer.toNat + 32 → state.memaddrs address)
    (budget : 40 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (evmInitAt 42)
    state.clock ≤ evaluated.2.clock + 40 ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  have safeNull : AllocationPlanSafe pointer [24] :=
    (allocationPlan_safe_aligned [24] pointer aligned
      (by intro size member; simp only [List.mem_singleton] at member; subst size; decide)
      (by change pointer.toNat + (24 + 0) ≤ 33806089496; omega)).1
  obtain ⟨middle,firstRun,firstCost,firstRemaining,firstCode,firstDomain,_,firstGlobals,_⟩ :=
    evaluate_globalAllocation_zero_prefix state (ofString "null_address") pointer 24 oldNull (evmInitAt 44)
      code heap nullSlot (by decide) safeNull aligned (by change pointer.toNat + 24 ≤ 33806089496; omega)
      (by intro address lower upper; apply arena address lower; change address.toNat < pointer.toNat + 24 at upper; omega)
      (by change 26 ≤ state.clock; omega)
  have middlePointer : (allocationEnd pointer 24).toNat = pointer.toNat + 24 := by
    exact allocationEnd_aligned_toNat pointer 24 (by change pointer.toNat + 24 ≤ 33806089496; omega) aligned (by decide)
  have middleAligned : (allocationEnd pointer 24).toNat % 8 = 0 := by
    rw [middlePointer]
    omega
  have middleHeap : middle.globals.lookup (ofString "heap_ptr") =
      some (.val (.word (allocationEnd pointer 24))) := by
    rw [firstGlobals]
    simp [globalAllocationGlobals,HolFiniteMapExact.lookup_update,FUPDATE,ofString]
  have middleEmpty : middle.globals.lookup (ofString "evm_empty") =
      some (.val (.word oldEmpty)) := by
    rw [firstGlobals]
    simpa [globalAllocationGlobals,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using emptySlot
  have safeEmpty : AllocationPlanSafe (allocationEnd pointer 24) [8] :=
    (allocationPlan_safe_aligned [8] (allocationEnd pointer 24) middleAligned
      (by intro size member; simp only [List.mem_singleton] at member; subst size; decide)
      (by rw [middlePointer]; change pointer.toNat + 24 + (8 + 0) ≤ 33806089496; omega)).1
  have firstSpent : state.clock ≤ middle.clock + 26 := firstCost
  obtain ⟨next,secondRun,secondCost,secondRemaining,secondCode,_,_,_,_⟩ :=
    evaluate_globalAllocation_zero_prefix middle (ofString "evm_empty") (allocationEnd pointer 24)
      8 oldEmpty (evmInitAt 46) (firstCode.trans code) middleHeap middleEmpty (by decide)
      safeEmpty middleAligned (by rw [middlePointer]; change pointer.toNat + 24 + 8 ≤ 33806089496; omega)
      (by
        intro address lower upper
        rw [firstDomain]
        apply arena address
        · rw [middlePointer] at lower; omega
        · rw [middlePointer] at upper; change address.toNat < pointer.toNat + 24 + 8 at upper; omega)
      (by change 10 ≤ middle.clock; omega)
  have secondSpent : middle.clock ≤ next.clock + 10 := secondCost
  have tail := evmInit_final_allocations_bounded next
    (secondCode.trans (firstCode.trans code)) (by omega)
  have actualRun : evaluateHOLFiniteState state (evmInitAt 42) =
      evaluateHOLFiniteState next (evmInitAt 46) := by
    change evaluateHOLFiniteState state (evmInitAt 42) = _
    rw [source_evmInit_null_zero]
    change evaluateHOLFiniteState state (globalAllocationProgram _ _) = _
    rw [firstRun,source_evmInit_empty_zero]
    exact secondRun
  change state.clock ≤ (evaluateHOLFiniteState state (evmInitAt 42)).2.clock + 40 ∧
    (evaluateHOLFiniteState state (evmInitAt 42)).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState state (evmInitAt 42)).1 ≠ some .timeOut
  rw [actualRun]
  exact ⟨by omega,by omega,tail.2.2⟩

#print axioms evaluate_evmInit_zero_suffix_bounded
end InitECandidate.Runtime
