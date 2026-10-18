import InitECandidate.Runtime.ForkInitBodyBound
import InitECandidate.Runtime.ForkInitSuffixGlobals
import InitECandidate.Runtime.InitializerCounterPrefixes
import InitECandidate.Runtime.ReachesReturnedContinuation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def forkInitAllocations : List (MlS × BitVec 64) :=
  [(ofString "zero32",32),(ofString "precompile_addrs",360)] ++ forkSuffixAllocations

/-- A returned original fork initializer installs the exact ten allocation
bindings and advances its initial aligned heap by 592 bytes. -/
theorem evaluate_forkInit_body_returned_globals {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer oldZero oldPrecompile : BitVec 64) (value : ValueHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (zeroSlot : state.globals.lookup (ofString "zero32") = some (.val (.word oldZero)))
    (precompileSlot : state.globals.lookup (ofString "precompile_addrs") = some (.val (.word oldPrecompile)))
    (words : ∀ entry ∈ forkSuffixAllocations, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (aligned : pointer.toNat % 8 = 0)
    (small : pointer.toNat + 592 ≤ 33806089496)
    (arena : ∀ address : BitVec 64, pointer.toNat ≤ address.toNat →
      address.toNat < pointer.toNat + 392 → state.memaddrs address)
    (budget : 515 ≤ state.clock)
    (returned : (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_fork_init)).1 = some (.returned value)) :
    value = .val (.word 0) ∧
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_fork_init)).2.globals =
      globalAllocationGlobals state.globals pointer forkInitAllocations ∧
    ∃ finalHeap : BitVec 64,
      (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_fork_init)).2.globals.lookup (ofString "heap_ptr") =
        some (.val (.word finalHeap)) ∧ finalHeap.toNat = pointer.toNat + 592 := by
  have safeZero : AllocationPlanSafe pointer [32] :=
    (allocationPlan_safe_aligned [32] pointer aligned
      (by intro size member; simp only [List.mem_singleton] at member; subst size; decide)
      (by change pointer.toNat + (32 + 0) ≤ 33806089496; omega)).1
  obtain ⟨middle,firstRun,firstCost,firstRemaining,firstCode,firstDomain,_,firstGlobals,_⟩ :=
    evaluate_globalAllocation_zero_prefix state (ofString "zero32") pointer 32 oldZero (forkInitAt 2)
      code heap zeroSlot (by decide) safeZero aligned (by change pointer.toNat + 32 ≤ 33806089496; omega)
      (by intro address lower upper; apply arena address lower; change address.toNat < pointer.toNat + 32 at upper; omega)
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
  obtain ⟨next,secondRun,secondCost,secondRemaining,secondCode,secondDomain,_,secondGlobals,_⟩ :=
    evaluate_globalAllocation_zero_prefix middle (ofString "precompile_addrs") (allocationEnd pointer 32)
      360 oldPrecompile (forkInitAt 4) (firstCode.trans code) middleHeap middleSlot (by decide)
      safePrecompile middleAligned (by rw [middlePointer]; change pointer.toNat + 32 + 360 ≤ 33806089496; omega)
      (by
        intro address lower upper
        rw [firstDomain]
        apply arena address
        · rw [middlePointer] at lower; omega
        · rw [middlePointer] at upper; change address.toNat < pointer.toNat + 32 + 360 at upper; omega)
      (by change 362 ≤ middle.clock; omega)
  have secondSpent : middle.clock ≤ next.clock + 362 := secondCost
  have actualRun : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_fork_init) =
      evaluateHOLFiniteState next (forkInitAt 4) := by
    change evaluateHOLFiniteState state (forkInitAt 0) = _
    rw [source_forkInit_zero32]
    change evaluateHOLFiniteState state (globalAllocationProgram _ _) = _
    rw [firstRun,evaluate_forkInit_precompile_normalized]
    exact secondRun
  have normal : (evaluateHOLFiniteState next (forkInitAt 4)).1 = some (.returned value) :=
    (congrArg Prod.fst actualRun).symm.trans returned
  obtain ⟨ready,frame,_,_,agreement,readyReturned⟩ :=
    reaches_returned_continuation next (forkInitAt 4) (forkInitAt 6) (InitializerCounterFinished next 17)
      17 value (evaluate_forkInit_counter_prefix next (by omega)) normal
  let suffixStart := allocationEnd (allocationEnd pointer 32) 360
  have suffixNat : suffixStart.toNat = pointer.toNat + 392 := by
    have step := allocationEnd_aligned_toNat (allocationEnd pointer 32) 360
      (by rw [middlePointer]; change pointer.toNat + 32 + 360 ≤ 33806089496; omega) middleAligned (by decide)
    change (allocationEnd (allocationEnd pointer 32) 360).toNat = _
    rw [step,middlePointer]
    change pointer.toNat + 32 + 360 = pointer.toNat + 392
    omega
  have suffixHeap : ready.globals.lookup (ofString "heap_ptr") = some (.val (.word suffixStart)) := by
    rw [frame.1,secondGlobals]
    simp [suffixStart,globalAllocationGlobals,HolFiniteMapExact.lookup_update,FUPDATE,ofString]
  have distinct : ∀ entry ∈ forkSuffixAllocations,
      entry.1 ≠ ofString "heap_ptr" ∧ entry.1 ≠ ofString "zero32" ∧ entry.1 ≠ ofString "precompile_addrs" := by decide
  have suffixWords : ∀ entry ∈ forkSuffixAllocations, ∃ word : BitVec 64,
      ready.globals.lookup entry.1 = some (.val (.word word)) := by
    intro entry member
    obtain ⟨word,binding⟩ := words entry member
    obtain ⟨notHeap,notZero,notPrecompile⟩ := distinct entry member
    refine ⟨word,?_⟩
    rw [frame.1,secondGlobals,firstGlobals]
    simpa [globalAllocationGlobals,HolFiniteMapExact.lookup_update,FUPDATE,
      Ne.symm notHeap,Ne.symm notZero,Ne.symm notPrecompile] using binding
  have readyRun : evaluateHOLFiniteState ready (forkInitAt 6) =
      (some (.returned value),(evaluateHOLFiniteState ready (forkInitAt 6)).2) :=
    Prod.ext readyReturned rfl
  obtain ⟨zero,globals,finalHeap,heapEnd,heapNat⟩ := evaluate_forkInit_suffix_returned_globals ready _ suffixStart value
    (frame.2.1.trans (secondCode.trans (firstCode.trans code))) suffixHeap suffixWords
    (by rw [suffixNat]; omega) (by rw [suffixNat]; omega) readyRun
  refine ⟨zero,?_,finalHeap,?_,?_⟩
  · rw [actualRun,agreement.2.2.2.1,globals,frame.1,secondGlobals,firstGlobals]
    simp only [forkInitAllocations,List.cons_append,List.nil_append,globalAllocationGlobals,suffixStart]
  · rw [actualRun,agreement.2.2.2.1]
    exact heapEnd
  · rw [suffixNat] at heapNat
    omega

#print axioms evaluate_forkInit_body_returned_globals
end InitECandidate.Runtime
