import InitECandidate.Runtime.MptInitBodyBound
import InitECandidate.Runtime.MptInitFinishBoundCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
theorem evaluate_mptInit_body_bounded_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (stateGlobal : state.globals.lookup (ofString "keccak_st") = some (.val (.word 2713714976)))
    (padGlobal : state.globals.lookup (ofString "keccak_pad") = some (.val (.word 2713715176)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713717456)))
    (words : ∀ entry ∈ mptInitAllocations, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (code : state.code = originalRuntimeCode) (budget : 724 ≤ state.clock)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → 2713714688 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_mpt_init)
    state.clock ≤ evaluated.2.clock + 724 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut ∧
      evaluated.2.globals = globalAllocationGlobals state.globals 2713717456 mptInitAllocations := by
  obtain ⟨ready,run,clock,_,_,installed,domain,globals,_⟩ :=
    evaluate_globalAllocation_prefix state mptInitAllocations mptInitFinish 2713717456 code heap (by decide) words
      (by simp only [mptInitAllocations,List.map_cons,List.map_nil,AllocationPlanSafe]; decide)
      (by change 5 ≤ state.clock; omega)
  have stateReady : ready.globals.lookup (ofString "keccak_st") = some (.val (.word 2713714976)) := by
    rw [globals,globalAllocationGlobals_lookup_other _ _ _ _ (by decide) (by decide)]
    exact stateGlobal
  have padReady : ready.globals.lookup (ofString "keccak_pad") = some (.val (.word 2713715176)) := by
    rw [globals,globalAllocationGlobals_lookup_other _ _ _ _ (by decide) (by decide)]
    exact padGlobal
  have pointers := mptInit_allocation_globals state.globals
  have tail := evaluate_mptInit_finish_bounded_cells ready stateReady padReady
    (by rw [globals]; exact pointers.1) (by rw [globals]; exact pointers.2.1)
    (by rw [globals]; exact pointers.2.2.1) (installed.trans code)
    (by change ready.clock = state.clock - 5 at clock; omega)
    (by intro address aligned lower upper; rw [domain]; exact arena address aligned lower upper)
  have retained := mptInit_finish_globals_frame ready (installed.trans code)
  rw [source_mptInit_body,run]
  refine ⟨?_,?_,tail.2.2,retained.trans globals⟩
  · have consumed := tail.1
    change ready.clock = state.clock - 5 at clock
    omega
  · have remaining := tail.2.1
    change ready.clock = state.clock - 5 at clock
    omega

#print axioms evaluate_mptInit_body_bounded_cells
end InitECandidate.Runtime
