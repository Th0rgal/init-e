import InitECandidate.Runtime.PackBytesMemoryBound
import InitECandidate.Runtime.AllocationDeclarationReach
import InitECandidate.Runtime.ReachesTerminalBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def packBytesBodyCost : Nat := 2 + (merkleMemoryCallCost + merkleMemoryCallCost)

theorem runBounded_packBytes_alloc {F : Type} (state : PanSemStateFiniteExact 64 F)
    (p n heap : BitVec 64)
    (hp : state.locals.lookup (ofString "p") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (hc : state.locals.lookup (ofString "count") = some (.val (.word (packBytesCount n))))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (small : n.toNat ≤ 134217712) (heapBound : heap.toNat ≤ 33806089496)
    (code : state.code = originalRuntimeCode) (budget : packBytesBodyCost ≤ state.clock) :
    RunBounded state (packBytesAt 1) packBytesBodyCost := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.panop .mul [.var .local (ofString "count"),.const 32]] =
      some [.val (.word (packBytesCount n * (32#64)))] := by
    simp [evalListHOLExact,evalHOLExact,hc,panOpHOL,valueIsWord,valueWord]
  have reached := evaluate_allocation_declaration_reaches state
    (.panop .mul [.var .local (ofString "count"),.const 32]) (ofString "buf") heap
    (packBytesCount n * (32#64)) (packBytesAt 2) args code hh heapBound
    (by unfold packBytesBodyCost at budget; omega)
  rw [← source_packBytes_alloc] at reached
  exact evaluate_reaches_terminal_bounded state (packBytesAt 1) (packBytesAt 2)
    (AllocationDeclarationReady state (ofString "buf") heap (packBytesCount n * (32#64)))
    2 (merkleMemoryCallCost + merkleMemoryCallCost) budget reached (by
      intro next allocated remaining
      have keep (key : MlS) (different : key ≠ ofString "buf") : next.locals.lookup key = state.locals.lookup key := by
        rw [allocated.1]; simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
      apply runBounded_packBytes_memory next heap p n
      · rw [allocated.1]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
      · exact (keep _ (by decide)).trans hp
      · exact (keep _ (by decide)).trans hn
      · exact (keep _ (by decide)).trans hc
      · exact small
      · exact allocated.2.2.1.trans code
      · exact remaining)

theorem runBounded_packBytes_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (p n heap : BitVec 64)
    (hp : state.locals.lookup (ofString "p") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (small : n.toNat ≤ 134217712) (heapBound : heap.toNat ≤ 33806089496)
    (code : state.code = originalRuntimeCode) (budget : packBytesBodyCost ≤ state.clock) :
    RunBounded state (sourceFunctionBody Guest.guestFn_pack_bytes) packBytesBodyCost := by
  rw [sourceFunctionBody_eq_structural]
  change RunBounded state (packBytesAt 0) packBytesBodyCost
  rw [source_packBytes_count]
  have initialized : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.shift .lsr (.op .add [.var .local (ofString "n"),.const 31]) (.const 5)) =
      some (.val (.word (packBytesCount n))) := by
    simp [packBytesCount,evalHOLExact,evalListHOLExact,hn,wordOpHOL,wordOp,valueIsWord,valueWord,wordShiftHOL]
  apply RunBounded.decWord state (ofString "count") _ (packBytesCount n) initialized
  apply runBounded_packBytes_alloc
    (setVarHOLFinite (ofString "count") (.val (.word (packBytesCount n))) state) p n heap
  · simpa (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using hp
  · simpa (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using hn
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · exact hh
  · exact small
  · exact heapBound
  · exact code
  · exact budget

#print axioms runBounded_packBytes_alloc
#print axioms runBounded_packBytes_body
end InitECandidate.Runtime
