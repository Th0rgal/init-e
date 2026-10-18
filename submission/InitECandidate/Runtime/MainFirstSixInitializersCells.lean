import InitECandidate.Runtime.MainFirstSixInitializers
import InitECandidate.Runtime.MainFirstFiveInitializersCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
theorem evaluate_main_first_six_initializers_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (oldHeap oldScratch oldFrame : BitVec 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word oldHeap)))
    (scratch : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word oldScratch)))
    (frame : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word oldFrame)))
    (hashWords : ∀ entry ∈ sha256InitAllocations ++ keccakInitAllocations, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (sszWords : ∀ entry ∈ sszInitAllocations, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (mptWords : ∀ entry ∈ mptInitAllocations, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (zeroHashes : state.globals.lookup (ofString "zero_hashes") = some (.val (.word 0)))
    (zeroWorkspace : state.globals.lookup (ofString "u256_ws") = some (.val (.word 0)))
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → 2713714688 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (code : state.code = originalRuntimeCode) (budget : 739 ≤ state.clock) :
    Reaches state (mainAt 0) (FirstSixInitializerContinuation state) 739 (mainAt 6) := by
  have reached := evaluate_main_first_five_initializers_cells state oldHeap oldScratch oldFrame heap scratch frame
    hashWords sszWords mptWords zeroHashes arena code (by omega)
  rcases reached with ⟨middle,valid,cost,remaining,agreement⟩ | abort
  · obtain ⟨globals,installed,domain,locals,midHeap⟩ := valid
    have midZero : middle.globals.lookup (ofString "u256_ws") = some (.val (.word 0)) := by
      rw [globals,globalAllocationGlobals_lookup_other _ _ _ _ (by decide) (by decide)]
      have equal := firstFourInitializerGlobals_mpt_workspace state.globals (ofString "u256_ws",0) (by decide)
      exact equal.trans zeroWorkspace
    have enough : 2 ≤ middle.clock := by omega
    obtain ⟨next,prefixRun,clock,nextCode,nextDomain,nextLocals,_,nextGlobals,nextHeap⟩ :=
      evaluate_main_workspaceInit_prefix middle (installed.trans code) midHeap midZero enough
    left
    refine ⟨next,⟨?_,nextCode.trans installed,nextDomain.trans domain,nextLocals.trans locals,nextHeap⟩,
      by omega,by omega,?_⟩
    · rw [nextGlobals,globals]
      rfl
    · rw [prefixRun] at agreement
      exact agreement
  · right
    exact stAbort_mono state _ 737 739 (by omega) abort

#print axioms evaluate_main_first_six_initializers_cells
end InitECandidate.Runtime
