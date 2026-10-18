import InitECandidate.Runtime.HtrWithdrawalSuffixBound
import InitECandidate.Runtime.AllocationDeclarationReach
import InitECandidate.Runtime.ReachesTerminalBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def htrWithdrawalAllocationCost : Nat := 2 + withdrawalCallsCost

theorem runBounded_htrWithdrawal_allocation {F : Type} (state : PanSemStateFiniteExact 64 F)
    (w out heap : BitVec 64)
    (hw : state.locals.lookup (ofString "w") = some (.val (.word w)))
    (ho : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : htrWithdrawalAllocationCost ≤ state.clock) :
    RunBounded state (htrWithdrawalAt 1) htrWithdrawalAllocationCost := by
  have reached := evaluate_allocation_declaration_reaches state (.panop .mul [.const 4,.const 32])
    (ofString "ch") heap (128#64) (htrWithdrawalAt 2) rfl code hh heapBound
    (by unfold htrWithdrawalAllocationCost at budget; omega)
  rw [← source_htrWithdrawal_alloc] at reached
  exact evaluate_reaches_terminal_bounded state (htrWithdrawalAt 1) (htrWithdrawalAt 2)
    (AllocationDeclarationReady state (ofString "ch") heap (128#64)) 2 withdrawalCallsCost budget reached (by
      intro next allocated remaining
      have keep (key : MlS) (different : key ≠ ofString "ch") : next.locals.lookup key = state.locals.lookup key := by
        rw [allocated.1]; simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
      apply withdrawal_calls_suffix next w heap out (allocationEnd heap (128#64))
      · refine ⟨(keep _ (by decide)).trans hw,?_,(keep _ (by decide)).trans ho⟩
        rw [allocated.1]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
      · rw [allocated.2.2.2.2.1]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      · exact allocated.2.2.2.2.2.1
      · exact allocated.2.2.1.trans code
      · exact remaining)

#print axioms runBounded_htrWithdrawal_allocation
end InitECandidate.Runtime
