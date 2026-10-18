import InitECandidate.Runtime.ProgressiveCounterDeclarationsBound
import InitECandidate.Runtime.AllocationDeclarationReach
import InitECandidate.Runtime.ReachesTerminalBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem source_progressive_acc : progressiveAt 2 =
    .decCall (ofString "acc") .one (ofString "alloc") [.const 32] (progressiveAt 3) := by rfl

theorem source_progressive_roots : progressiveAt 1 =
    .decCall (ofString "roots") .one (ofString "alloc")
      [.panop .mul [.const 24,.const 32]] (progressiveAt 2) := by rfl

theorem runBounded_progressive_acc {F : Type} (state : PanSemStateFiniteExact 64 F)
    (p n roots heap : BitVec 64)
    (hp : state.locals.lookup (ofString "p") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (hr : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (small : n.toNat ≤ 134217712) (heapBound : heap.toNat ≤ 33806089496)
    (code : state.code = originalRuntimeCode) (budget : 2 + progressiveLoopsCost ≤ state.clock) :
    RunBounded state (progressiveAt 2) (2 + progressiveLoopsCost) := by
  have reached := evaluate_allocation_declaration_reaches state (.const 32) (ofString "acc") heap (32#64)
    (progressiveAt 3) rfl code hh heapBound (by omega)
  rw [← source_progressive_acc] at reached
  exact evaluate_reaches_terminal_bounded state (progressiveAt 2) (progressiveAt 3)
    (AllocationDeclarationReady state (ofString "acc") heap (32#64)) 2 progressiveLoopsCost budget reached (by
      intro next allocated remaining
      have keep (key : MlS) (different : key ≠ ofString "acc") : next.locals.lookup key = state.locals.lookup key := by
        rw [allocated.1]
        simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
      apply runBounded_progressive_counters next p n roots (allocationEnd heap (32#64))
        ((keep _ (by decide)).trans hp) ((keep _ (by decide)).trans hn) ((keep _ (by decide)).trans hr)
      · rw [allocated.2.2.2.2.1]
        simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      · exact small
      · exact allocated.2.2.2.2.2.1
      · exact allocated.2.2.1.trans code
      · exact remaining)

theorem runBounded_progressive_roots {F : Type} (state : PanSemStateFiniteExact 64 F)
    (p n heap : BitVec 64)
    (hp : state.locals.lookup (ofString "p") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (small : n.toNat ≤ 134217712) (heapBound : heap.toNat ≤ 33806089496)
    (code : state.code = originalRuntimeCode) (budget : 2 + (2 + progressiveLoopsCost) ≤ state.clock) :
    RunBounded state (progressiveAt 1) (2 + (2 + progressiveLoopsCost)) := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.panop .mul [.const 24,.const 32]] = some [.val (.word (768#64))] := by rfl
  have reached := evaluate_allocation_declaration_reaches state (.panop .mul [.const 24,.const 32])
    (ofString "roots") heap (768#64) (progressiveAt 2) args code hh heapBound (by omega)
  rw [← source_progressive_roots] at reached
  exact evaluate_reaches_terminal_bounded state (progressiveAt 1) (progressiveAt 2)
    (AllocationDeclarationReady state (ofString "roots") heap (768#64)) 2 (2 + progressiveLoopsCost) budget reached (by
      intro next allocated remaining
      have keep (key : MlS) (different : key ≠ ofString "roots") : next.locals.lookup key = state.locals.lookup key := by
        rw [allocated.1]
        simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
      apply runBounded_progressive_acc next p n heap (allocationEnd heap (768#64))
        ((keep _ (by decide)).trans hp) ((keep _ (by decide)).trans hn)
      · rw [allocated.1]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
      · rw [allocated.2.2.2.2.1]
        simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      · exact small
      · exact allocated.2.2.2.2.2.1
      · exact allocated.2.2.1.trans code
      · exact remaining)

#print axioms source_progressive_acc
#print axioms source_progressive_roots
#print axioms runBounded_progressive_acc
#print axioms runBounded_progressive_roots
end InitECandidate.Runtime
