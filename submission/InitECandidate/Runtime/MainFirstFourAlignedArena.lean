import InitECandidate.Runtime.MainFirstFourInitializers
import InitECandidate.Runtime.SszInitAlignedArena
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
/-- Actual main through SSZ initialization, including fixed allocation guards
and table-store domains. No input-dependent reserve is required. -/
theorem evaluate_main_first_four_initializers_aligned {F : Type} (state : PanSemStateFiniteExact 64 F)
    (oldHeap oldScratch oldFrame : BitVec 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word oldHeap)))
    (scratch : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word oldScratch)))
    (frame : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word oldFrame)))
    (hashWords : ∀ entry ∈ sha256InitAllocations ++ keccakInitAllocations, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (sszWords : ∀ entry ∈ sszInitAllocations, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (zero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word 0)))
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → 2713715312 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (code : state.code = originalRuntimeCode) (budget : 12 ≤ state.clock) :
    ∃ ready : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (mainAt 0) = evaluateHOLFiniteState ready (mainAt 4) ∧
      ready.clock = state.clock - 12 ∧ ready.memory = memWrites state.memory 2713715408 sszInitCells ∧
      ready.locals = state.locals ∧ ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧
      ready.globals = globalAllocationGlobals
        (globalAllocationGlobals (globalAllocationGlobals (memInitReady state).globals 2713714688 sha256InitAllocations)
          2713714976 keccakInitAllocations) 2713715312 sszInitAllocations ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713717456)) ∧
      ready.globals.lookup (ofString "ssz_offs") = some (.val (.word 2713715344)) ∧
      ready.globals.lookup (ofString "zero_hashes") = some (.val (.word 2713715408)) := by
  obtain ⟨middle,prefixRun,clock,memory,locals,installed,domain,globals,midHeap⟩ :=
    evaluate_main_first_initializers state oldHeap oldScratch oldFrame heap scratch frame hashWords code (by omega)
  have preserved : ∀ entry ∈ sszInitAllocations, middle.globals.lookup entry.1 = state.globals.lookup entry.1 := by
    intro entry member
    have distinct : ∀ entry ∈ sszInitAllocations,
        entry.1 ≠ ofString "heap_ptr" ∧ entry.1 ≠ ofString "scratch_ptr" ∧ entry.1 ≠ ofString "frame_mem_ptr" ∧
        (∀ other ∈ sha256InitAllocations, entry.1 ≠ other.1) ∧
        (∀ other ∈ keccakInitAllocations, entry.1 ≠ other.1) := by decide
    obtain ⟨notHeap,notScratch,notFrame,notSha,notKeccak⟩ := distinct entry member
    rw [globals,globalAllocationGlobals_lookup_other _ _ _ _ notHeap notKeccak,
      globalAllocationGlobals_lookup_other _ _ _ _ notHeap notSha]
    simp [memInitReady,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      Ne.symm notHeap,Ne.symm notScratch,Ne.symm notFrame]
  have midZero : middle.globals.lookup (ofString "zero_hashes") = some (.val (.word 0)) := by
    have equal := preserved (ofString "zero_hashes",2048) (by decide)
    exact equal.trans zero
  have midWords : ∀ entry ∈ sszInitAllocations, ∃ word : BitVec 64,
      middle.globals.lookup entry.1 = some (.val (.word word)) := by
    intro entry member
    obtain ⟨word,present⟩ := sszWords entry member
    exact ⟨word,(preserved entry member).trans present⟩
  obtain ⟨ready,sszCall,sszClock,sszMemory,sszLocals,sszCode,sszDomain,sszGlobals,finalHeap,offsets,hashes⟩ :=
    evaluate_sszInit_after_hash_initializers_aligned middle (installed.trans code) midHeap midZero midWords
      (by intro address aligned lower upper; rw [domain]; exact arena address aligned lower upper) (by omega)
  refine ⟨ready,?_,by omega,?_,sszLocals.trans locals,sszCode.trans installed,sszDomain.trans domain,?_,finalHeap,offsets,hashes⟩
  · rw [prefixRun,source_main_sszInit_call,evaluateHOLFiniteState_seq_line780,sszCall]
  · rw [sszMemory,memory]
  · rw [sszGlobals,globals]

#print axioms evaluate_main_first_four_initializers_aligned
end InitECandidate.Runtime
