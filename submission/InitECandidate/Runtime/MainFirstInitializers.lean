import InitECandidate.Runtime.MainHashInitPrefix
import InitECandidate.Runtime.MemInitCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The real first three main initializers reach SSZ initialization in eight
ticks. Their fixed allocations fit directly in the initialized arena. -/
theorem evaluate_main_first_initializers {F : Type} (state : PanSemStateFiniteExact 64 F)
    (oldHeap oldScratch oldFrame : BitVec 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word oldHeap)))
    (scratch : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word oldScratch)))
    (frame : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word oldFrame)))
    (words : ∀ entry ∈ sha256InitAllocations ++ keccakInitAllocations, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (code : state.code = originalRuntimeCode) (budget : 8 ≤ state.clock) :
    ∃ ready : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (mainAt 0) = evaluateHOLFiniteState ready (mainAt 3) ∧
      ready.clock = state.clock - 8 ∧ ready.memory = state.memory ∧ ready.locals = state.locals ∧
      ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧
      ready.globals = globalAllocationGlobals
        (globalAllocationGlobals (memInitReady state).globals 2713714688 sha256InitAllocations)
        2713714976 keccakInitAllocations ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713715312)) := by
  let initialized : PanSemStateFiniteExact 64 F :=
    {memInitReady {state with clock := state.clock - 1} with locals := state.locals}
  have initializedHeap : initialized.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713714688)) := by
    simp [initialized,memInitReady,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "frame_mem_ptr" ≠ ofString "heap_ptr" by decide,
      show ofString "scratch_ptr" ≠ ofString "heap_ptr" by decide]
  have initializedWords : ∀ entry ∈ sha256InitAllocations ++ keccakInitAllocations, ∃ word : BitVec 64,
      initialized.globals.lookup entry.1 = some (.val (.word word)) := by
    intro entry member
    obtain ⟨word,present⟩ := words entry member
    have distinct : ∀ entry ∈ sha256InitAllocations ++ keccakInitAllocations,
        entry.1 ≠ ofString "heap_ptr" ∧ entry.1 ≠ ofString "scratch_ptr" ∧ entry.1 ≠ ofString "frame_mem_ptr" := by decide
    obtain ⟨notHeap,notScratch,notFrame⟩ := distinct entry member
    refine ⟨word,?_⟩
    simpa [initialized,memInitReady,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      Ne.symm notHeap,Ne.symm notScratch,Ne.symm notFrame] using present
  have shaEnd : allocationPlanEnd (2713714688 : BitVec 64) (sha256InitAllocations.map Prod.snd) = 2713714976 := by decide
  have finalEnd : allocationPlanEnd (allocationPlanEnd (2713714688 : BitVec 64) (sha256InitAllocations.map Prod.snd))
      (keccakInitAllocations.map Prod.snd) = 2713715312 := by decide
  obtain ⟨ready,run,clock,memory,locals,installed,domain,globals,finalHeap⟩ :=
    evaluate_main_hashInit_prefix initialized 2713714688 code initializedHeap initializedWords
      (by simp only [sha256InitAllocations,List.map_cons,List.map_nil,AllocationPlanSafe]; decide)
      (by simp only [keccakInitAllocations,List.map_cons,List.map_nil,AllocationPlanSafe]; decide)
      (by change 7 ≤ state.clock - 1; omega)
  refine ⟨ready,?_,?_,memory,locals,installed,domain,?_,?_⟩
  · rw [evaluate_main_memInit_prefix state oldHeap oldScratch oldFrame heap scratch frame code (by omega)]
    exact run
  · change ready.clock = state.clock - 1 - 7 at clock
    omega
  · rw [globals,shaEnd]
    rfl
  · rw [finalEnd] at finalHeap
    exact finalHeap

#print axioms evaluate_main_first_initializers
end InitECandidate.Runtime
