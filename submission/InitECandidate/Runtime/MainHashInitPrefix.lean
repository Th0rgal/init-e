import InitECandidate.Runtime.AllocationInitializersCallSuccess
import InitECandidate.Runtime.MainInputSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem source_main_sha256Init_call : mainAt 1 =
    .seq (.call (some (none,none)) (ofString "sha256_init") []) (mainAt 2) := by
  simp only [mainAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_main_keccakInit_call : mainAt 2 =
    .seq (.call (some (none,none)) (ofString "keccak_init") []) (mainAt 3) := by
  simp only [mainAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The next two actual main initializers reach SSZ initialization in seven
ticks, with the exact allocator updates and all caller memory retained. -/
theorem evaluate_main_hashInit_prefix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (words : ∀ entry ∈ sha256InitAllocations ++ keccakInitAllocations, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (shaSafe : AllocationPlanSafe pointer (sha256InitAllocations.map Prod.snd))
    (keccakSafe : AllocationPlanSafe (allocationPlanEnd pointer (sha256InitAllocations.map Prod.snd))
      (keccakInitAllocations.map Prod.snd))
    (budget : 7 ≤ state.clock) :
    ∃ ready : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (mainAt 1) = evaluateHOLFiniteState ready (mainAt 3) ∧
      ready.clock = state.clock - 7 ∧ ready.memory = state.memory ∧ ready.locals = state.locals ∧
      ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧
      ready.globals = globalAllocationGlobals
        (globalAllocationGlobals state.globals pointer sha256InitAllocations)
        (allocationPlanEnd pointer (sha256InitAllocations.map Prod.snd)) keccakInitAllocations ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word
        (allocationPlanEnd (allocationPlanEnd pointer (sha256InitAllocations.map Prod.snd))
          (keccakInitAllocations.map Prod.snd)))) := by
  obtain ⟨middle,shaCall,shaClock,shaMemory,shaLocals,shaCode,shaDomain,shaGlobals,shaHeap⟩ :=
    evaluate_sha256Init_call_success state pointer code heap
      (fun entry member => words entry (List.mem_append_left _ member)) shaSafe (by omega)
  have nextWords : ∀ entry ∈ keccakInitAllocations, ∃ word : BitVec 64,
      middle.globals.lookup entry.1 = some (.val (.word word)) := by
    intro entry member
    obtain ⟨word,present⟩ := words entry (List.mem_append_right _ member)
    refine ⟨word,?_⟩
    rw [shaGlobals,globalAllocationGlobals_lookup_other]
    · exact present
    · have different : ∀ entry ∈ keccakInitAllocations, entry.1 ≠ ofString "heap_ptr" := by decide
      exact different entry member
    · have separate : ∀ entry ∈ keccakInitAllocations, ∀ other ∈ sha256InitAllocations, entry.1 ≠ other.1 := by decide
      exact separate entry member
  obtain ⟨ready,keccakCall,keccakClock,keccakMemory,keccakLocals,keccakCode,keccakDomain,keccakGlobals,keccakHeap⟩ :=
    evaluate_keccakInit_call_success middle _ (shaCode.trans code) shaHeap nextWords keccakSafe (by omega)
  refine ⟨ready,?_,by omega,keccakMemory.trans shaMemory,keccakLocals.trans shaLocals,
    keccakCode.trans shaCode,keccakDomain.trans shaDomain,?_,keccakHeap⟩
  · rw [source_main_sha256Init_call,evaluateHOLFiniteState_seq_line780,shaCall]
    change evaluateHOLFiniteState middle (mainAt 2) = _
    rw [source_main_keccakInit_call,evaluateHOLFiniteState_seq_line780,keccakCall]
  · rw [keccakGlobals,shaGlobals]

#print axioms source_main_sha256Init_call
#print axioms source_main_keccakInit_call
#print axioms evaluate_main_hashInit_prefix
end InitECandidate.Runtime
