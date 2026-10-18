import InitECandidate.Runtime.HtrPcontainerSuffixBound
import InitECandidate.Runtime.ProgressiveCallBound
import InitECandidate.Runtime.AllocationDeclarationReach
import InitECandidate.Runtime.ReachesTerminalBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def htrPcontainerProgressiveCost : Nat := (progressiveBodyCost + 1) + htrPcontainerSuffixCost

def htrPcontainerAllocationCost : Nat := 2 + htrPcontainerProgressiveCost

theorem runBounded_htrPcontainer_progressive {F : Type} (state : PanSemStateFiniteExact 64 F)
    (ch n tmp heap : BitVec 64)
    (hc : state.locals.lookup (ofString "ch") = some (.val (.word ch)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (ht : state.locals.lookup (ofString "tmp") = some (.val (.word tmp)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (small : n.toNat ≤ 134217712) (heapBound : heap.toNat ≤ 33806089496)
    (code : state.code = originalRuntimeCode) (budget : htrPcontainerProgressiveCost ≤ state.clock) :
    RunBounded state (htrPcontainerAt 2) htrPcontainerProgressiveCost := by
  rw [source_htrPcontainer_progressive]
  exact RunBounded.seq (runBounded_progressive_call state none _ ch n tmp heap
    (by simp [evalListHOLExact,evalHOLExact,hc,hn,ht]) small hh heapBound code
    (by unfold htrPcontainerProgressiveCost at budget; omega)) budget (by
      intro next normal nextCode remaining
      exact RunBounded.ofProg htrPcontainer_suffix_bounded (nextCode.trans code) remaining)

theorem runBounded_htrPcontainer_allocation {F : Type} (state : PanSemStateFiniteExact 64 F)
    (ch n heap : BitVec 64)
    (hc : state.locals.lookup (ofString "ch") = some (.val (.word ch)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (small : n.toNat ≤ 134217712) (heapBound : heap.toNat ≤ 33806089496)
    (code : state.code = originalRuntimeCode) (budget : htrPcontainerAllocationCost ≤ state.clock) :
    RunBounded state (htrPcontainerAt 1) htrPcontainerAllocationCost := by
  have reached := evaluate_allocation_declaration_reaches state (.const 64) (ofString "tmp") heap (64#64)
    (htrPcontainerAt 2) rfl code hh heapBound (by unfold htrPcontainerAllocationCost at budget; omega)
  rw [← source_htrPcontainer_alloc] at reached
  exact evaluate_reaches_terminal_bounded state (htrPcontainerAt 1) (htrPcontainerAt 2)
    (AllocationDeclarationReady state (ofString "tmp") heap (64#64)) 2 htrPcontainerProgressiveCost budget reached (by
      intro next allocated remaining
      have keep (key : MlS) (different : key ≠ ofString "tmp") : next.locals.lookup key = state.locals.lookup key := by
        rw [allocated.1]; simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
      apply runBounded_htrPcontainer_progressive next ch n heap (allocationEnd heap (64#64))
        ((keep _ (by decide)).trans hc) ((keep _ (by decide)).trans hn)
      · rw [allocated.1]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
      · rw [allocated.2.2.2.2.1]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      · exact small
      · exact allocated.2.2.2.2.2.1
      · exact allocated.2.2.1.trans code
      · exact remaining)

#print axioms runBounded_htrPcontainer_progressive
#print axioms runBounded_htrPcontainer_allocation
end InitECandidate.Runtime
