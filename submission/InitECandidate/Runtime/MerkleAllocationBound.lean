import InitECandidate.Runtime.MerkleMemoryBound
import InitECandidate.Runtime.AllocationDeclarationReach
import InitECandidate.Runtime.ReachesTerminalBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def merkleAllocationCost : Nat := 2 + merkleMemorySuffixCost

theorem source_merkleAllocation : merkleizeAt 6 =
    .decCall (ofString "buf") .one (ofString "alloc")
      [.panop .mul [.var .local (ofString "size"),.const 32]] (merkleizeAt 7) := by rfl

/-- The original allocation either traps or supplies the real buffer pointer
to copy/zero/hash. No successful-reserve premise is assumed. -/
theorem runBounded_merkleAllocation {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer n size dn target heap : BitVec 64)
    (input : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (count : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (sizeLocal : state.locals.lookup (ofString "size") = some (.val (.word size)))
    (depth : state.locals.lookup (ofString "dn") = some (.val (.word dn)))
    (limit : state.locals.lookup (ofString "target") = some (.val (.word target)))
    (lengths : MerkleChunkLengths n size) (depthBound : dn.toNat ≤ 27) (targetBound : target.toNat ≤ 63)
    (heapLocal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : merkleAllocationCost ≤ state.clock) :
    RunBounded state (merkleizeAt 6) merkleAllocationCost := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.panop .mul [.var .local (ofString "size"),.const 32]] = some [.val (.word (size * (32#64)))] := by
    simp [evalListHOLFinite_eq_toExact,evalListHOLExact,evalHOLExact,sizeLocal,panOpHOL,valueIsWord,valueWord]
  have reached := evaluate_allocation_declaration_reaches state
    (.panop .mul [.var .local (ofString "size"),.const 32]) (ofString "buf") heap (size * (32#64))
    (merkleizeAt 7) args code heapLocal heapBound (by unfold merkleAllocationCost at budget; omega)
  rw [← source_merkleAllocation] at reached
  exact evaluate_reaches_terminal_bounded state (merkleizeAt 6) (merkleizeAt 7)
    (AllocationDeclarationReady state (ofString "buf") heap (size * (32#64)))
    2 merkleMemorySuffixCost budget reached (by
      intro next allocated remaining
      have keep (key : MlS) (different : key ≠ ofString "buf") :
          next.locals.lookup key = state.locals.lookup key := by
        rw [allocated.1]
        simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
      have buffer : next.locals.lookup (ofString "buf") = some (.val (.word heap)) := by
        rw [allocated.1]
        simp [HolFiniteMapExact.lookup_update,FUPDATE]
      exact runBounded_merkleMemorySuffix next heap pointer n size dn target buffer
        ((keep _ (by decide)).trans input) ((keep _ (by decide)).trans count)
        ((keep _ (by decide)).trans sizeLocal) ((keep _ (by decide)).trans depth)
        ((keep _ (by decide)).trans limit) lengths depthBound targetBound
        (allocated.2.2.1.trans code) remaining)

theorem source_merkleSize_declaration : merkleizeAt 5 =
    .dec (ofString "size") .one (.shift .lsl (.const 1) (.var .local (ofString "dn"))) (merkleizeAt 6) := by rfl

theorem runBounded_merkleSizeAllocation {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer n dn target heap : BitVec 64)
    (input : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (count : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (depth : state.locals.lookup (ofString "dn") = some (.val (.word dn)))
    (limit : state.locals.lookup (ofString "target") = some (.val (.word target)))
    (lengths : MerkleChunkLengths n ((1#64) <<< dn.toNat))
    (depthBound : dn.toNat ≤ 27) (targetBound : target.toNat ≤ 63)
    (heapLocal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : merkleAllocationCost ≤ state.clock) :
    RunBounded state (merkleizeAt 5) merkleAllocationCost := by
  have legal : ¬ (dn.toNat ≠ 0 ∧ 64 ≤ dn.toNat) := by omega
  have initialized : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.shift .lsl (.const 1) (.var .local (ofString "dn"))) =
      some (.val (.word ((1#64) <<< dn.toNat))) := by
    simp [evalHOLExact,depth,wordShiftHOL,legal]
  rw [source_merkleSize_declaration]
  apply RunBounded.decWord state (ofString "size") _ ((1#64) <<< dn.toNat) initialized
  apply runBounded_merkleAllocation _ pointer n ((1#64) <<< dn.toNat) dn target heap
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "size" ≠ ofString "p" by decide] using input
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "size" ≠ ofString "n" by decide] using count
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "size" ≠ ofString "dn" by decide] using depth
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "size" ≠ ofString "target" by decide] using limit
  · exact lengths
  · exact depthBound
  · exact targetBound
  · exact heapLocal
  · exact heapBound
  · exact code
  · exact budget

#print axioms source_merkleAllocation
#print axioms runBounded_merkleAllocation
#print axioms source_merkleSize_declaration
#print axioms runBounded_merkleSizeAllocation
end InitECandidate.Runtime
