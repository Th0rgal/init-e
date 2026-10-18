import InitECandidate.Runtime.EvmInitZeroSuffixSuccess
import InitECandidate.Runtime.AlignedCellDomains
import InitECandidate.Runtime.MemzeroAlignedCallCells
import InitECandidate.Runtime.KeccakShortCallBoundCells
import InitECandidate.Runtime.EvmInitZeroSuffixBoundCells
import InitECandidate.Runtime.GlobalAllocationZeroPrefixCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem evaluate_evmInit_zero_suffix_success_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer oldNull oldEmpty oldKey oldHeader : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (nullSlot : state.globals.lookup (ofString "null_address") = some (.val (.word oldNull)))
    (emptySlot : state.globals.lookup (ofString "evm_empty") = some (.val (.word oldEmpty)))
    (keySlot : state.globals.lookup (ofString "evm_key_buf") = some (.val (.word oldKey)))
    (headerSlot : state.globals.lookup (ofString "pre_hdr_buf") = some (.val (.word oldHeader)))
    (aligned : pointer.toNat % 8 = 0)
    (small : pointer.toNat + 160 ≤ 33806089496)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → pointer.toNat ≤ address.toNat →
      address.toNat < pointer.toNat + 32 → state.memaddrs address)
    (budget : 40 ≤ state.clock) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (evmInitAt 42) = (some (.returned (.val (.word 0))),post) ∧
      state.clock ≤ post.clock + 38 ∧ post.clock ≤ state.clock ∧
      post.globals = globalAllocationGlobals state.globals pointer evmZeroSuffixAllocations ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.locals = HolFiniteMapExact.empty ∧
      ∃ finalHeap : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
        finalHeap.toNat = pointer.toNat + 160 := by
  have safeNull : AllocationPlanSafe pointer [24] :=
    (allocationPlan_safe_aligned [24] pointer aligned
      (by intro size member; simp only [List.mem_singleton] at member; subst size; decide)
      (by change pointer.toNat + (24 + 0) ≤ 33806089496; omega)).1
  obtain ⟨middle,firstRun,firstCost,firstRemaining,firstCode,firstDomain,firstLocals,firstGlobals,_⟩ :=
    evaluate_globalAllocation_zero_prefix_cells state (ofString "null_address") pointer 24 oldNull (evmInitAt 44)
      code heap nullSlot (by decide) safeNull aligned (by change pointer.toNat + 24 ≤ 33806089496; omega)
      (by intro address cellAligned lower upper; apply arena address cellAligned lower; change address.toNat < pointer.toNat + 24 at upper; omega)
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
  obtain ⟨next,secondRun,secondCost,secondRemaining,secondCode,secondDomain,secondLocals,secondGlobals,_⟩ :=
    evaluate_globalAllocation_zero_prefix_cells middle (ofString "evm_empty") (allocationEnd pointer 24)
      8 oldEmpty (evmInitAt 46) (firstCode.trans code) middleHeap middleEmpty (by decide)
      safeEmpty middleAligned (by rw [middlePointer]; change pointer.toNat + 24 + 8 ≤ 33806089496; omega)
      (by
        intro address cellAligned lower upper
        rw [firstDomain]
        apply arena address cellAligned
        · rw [middlePointer] at lower; omega
        · rw [middlePointer] at upper; change address.toNat < pointer.toNat + 24 + 8 at upper; omega)
      (by change 10 ≤ middle.clock; omega)
  have secondSpent : middle.clock ≤ next.clock + 10 := secondCost
  let finalEntries : List (MlS × BitVec 64) := [(ofString "evm_key_buf",32),(ofString "pre_hdr_buf",96)]
  let finalStart := allocationEnd (allocationEnd pointer 24) 8
  have finalStartNat : finalStart.toNat = pointer.toNat + 32 := by
    have step := allocationEnd_aligned_toNat (allocationEnd pointer 24) 8
      (by rw [middlePointer]; change pointer.toNat + 24 + 8 ≤ 33806089496; omega) middleAligned (by decide)
    change (allocationEnd (allocationEnd pointer 24) 8).toNat = _
    rw [step,middlePointer]
    change pointer.toNat + 24 + 8 = pointer.toNat + 32
    omega
  have finalAligned : finalStart.toNat % 8 = 0 := by rw [finalStartNat]; omega
  have finalPlan := allocationPlan_safe_aligned [32,96] finalStart finalAligned
    (by intro size member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member; rcases member with rfl | rfl <;> decide)
    (by rw [finalStartNat]; change pointer.toNat + 32 + (32 + (96 + 0)) ≤ 33806089496; omega)
  have finalWords : ∀ entry ∈ finalEntries, ∃ word : BitVec 64,
      next.globals.lookup entry.1 = some (.val (.word word)) := by
    intro entry member
    simp only [finalEntries,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · refine ⟨oldKey,?_⟩
      rw [secondGlobals,firstGlobals]
      simpa [globalAllocationGlobals,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using keySlot
    · refine ⟨oldHeader,?_⟩
      rw [secondGlobals,firstGlobals]
      simpa [globalAllocationGlobals,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using headerSlot
  have finalHeap : next.globals.lookup (ofString "heap_ptr") = some (.val (.word finalStart)) := by
    rw [secondGlobals]
    simp [finalStart,globalAllocationGlobals,HolFiniteMapExact.lookup_update,FUPDATE,ofString]
  obtain ⟨post,run,clock,_,locals,installed,domain,globals,heapEnd⟩ :=
    evaluate_globalAllocation_return next finalEntries finalStart
      (secondCode.trans (firstCode.trans code)) finalHeap
      (by intro entry member; simp only [finalEntries,List.mem_cons,List.not_mem_nil,or_false] at member; rcases member with rfl | rfl <;> decide)
      finalWords finalPlan.1 (by change 2 ≤ next.clock; omega)
  have actual : evaluateHOLFiniteState state (evmInitAt 42) = (some (.returned (.val (.word 0))),post) := by
    rw [source_evmInit_null_zero]
    change evaluateHOLFiniteState state (globalAllocationProgram _ _) = _
    rw [firstRun,source_evmInit_empty_zero]
    change evaluateHOLFiniteState middle (globalAllocationProgram _ _) = _
    rw [secondRun,source_evmInit_final_allocations]
    exact run
  refine ⟨post,actual,?_,?_,?_,installed.trans (secondCode.trans firstCode),
    domain.trans (secondDomain.trans firstDomain),locals,allocationPlanEnd finalStart [32,96],heapEnd,?_⟩
  · change post.clock = next.clock - 2 at clock
    omega
  · change post.clock = next.clock - 2 at clock
    omega
  · rw [globals,secondGlobals,firstGlobals]
    rfl
  · rw [finalPlan.2,finalStartNat]
    rfl

#print axioms evaluate_evmInit_zero_suffix_success_cells
end InitECandidate.Runtime
