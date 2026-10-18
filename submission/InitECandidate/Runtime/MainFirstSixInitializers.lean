import InitECandidate.Runtime.MainFirstFiveInitializers
import InitECandidate.Runtime.MainWorkspaceInitPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def firstSixInitializerGlobals (globals : HolFiniteMapExact MlS (ValueHOL 64)) : HolFiniteMapExact MlS (ValueHOL 64) :=
  globalAllocationGlobals
    (globalAllocationGlobals (firstFourInitializerGlobals globals) 2713717456 mptInitAllocations)
    2713717640 u256WorkspaceAllocations

def FirstSixInitializerContinuation {F : Type} (state next : PanSemStateFiniteExact 64 F) : Prop :=
  next.globals = firstSixInitializerGlobals state.globals ∧ next.code = state.code ∧
    next.memaddrs = state.memaddrs ∧ next.locals = state.locals ∧
    next.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713718280))

/-- Actual main reaches secp initialization with the computed heap and
globals, or terminates early, within 739 source ticks. -/
theorem evaluate_main_first_six_initializers {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (arena : ∀ address : BitVec 64, 2713714688 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (code : state.code = originalRuntimeCode) (budget : 739 ≤ state.clock) :
    Reaches state (mainAt 0) (FirstSixInitializerContinuation state) 739 (mainAt 6) := by
  have reached := evaluate_main_first_five_initializers state oldHeap oldScratch oldFrame heap scratch frame
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

#print axioms evaluate_main_first_six_initializers
end InitECandidate.Runtime
