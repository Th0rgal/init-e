import InitECandidate.Runtime.ProgressiveAccMemory
import InitECandidate.Runtime.ProgressiveAllocationBound
import InitECandidate.Runtime.ReachesReturnedContinuation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem progressiveRoots_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator zeroHashes p n heap out mark watched : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (hp : state.locals.lookup (ofString "p") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (outAligned : out.toNat % 8 = 0) (outFits : out.toNat + 32 ≤ 33806089496)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (small : n.toNat ≤ 134217712)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496) (heapBefore : watched.toNat < heap.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : 2 + (2 + progressiveLoopsCost) ≤ state.clock)
    (run : evaluateHOLFiniteState state (progressiveAt 1) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have reached := evaluate_allocation_declaration_reaches state (.panop .mul [.const 24,.const 32]) (ofString "roots") heap (768#64)
    (progressiveAt 2) rfl code hh heapFits ((Nat.le_add_right 2 _).trans budget)
  rw [← source_progressive_roots] at reached
  obtain ⟨ready,allocated,spent,_,agreement,returned⟩ := reaches_returned_continuation state
    (progressiveAt 1) (progressiveAt 2) _ 2 value reached (by rw [run])
  have keep (key : MlS) (different : key ≠ ofString "roots") : ready.locals.lookup key = state.locals.lookup key := by
    rw [allocated.1]; simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have globalKeep (key : MlS) (different : key ≠ ofString "heap_ptr") : ready.globals.lookup key = state.globals.lookup key := by
    rw [allocated.2.2.2.2.1]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have atRoots : ready.locals.lookup (ofString "roots") = some (.val (.word heap)) := by
    rw [allocated.1]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have atHeap : ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd heap (768#64)))) := by
    rw [allocated.2.2.2.2.1]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have extent := allocated.2.2.2.2.2.2.1
  have endAligned := allocated.2.2.2.2.2.2.2
  have endFits := allocated.2.2.2.2.2.1
  have rootsFits : heap.toNat + 768 ≤ 33806089496 := by
    change heap.toNat + 768 ≤ (allocationEnd heap (768#64)).toNat at extent
    exact extent.trans endFits
  have remaining : 2 + progressiveLoopsCost ≤ ready.clock := by
    exact Nat.le_of_add_le_add_right
      ((show (2 + progressiveLoopsCost) + 2 ≤ state.clock from by simpa only [Nat.add_comm] using budget).trans spent)
  have suffixRun : evaluateHOLFiniteState ready (progressiveAt 2) =
      (some (.returned value),(evaluateHOLFiniteState ready (progressiveAt 2)).2) := Prod.ext returned rfl
  have suffix := progressiveAcc_returned_memory ready _ pointer accelerator zeroHashes p n heap
    (allocationEnd heap (768#64)) out mark watched value
    ((globalKeep _ (by decide)).trans atPointer) ((globalKeep _ (by decide)).trans atAccel)
    ((globalKeep _ (by decide)).trans atZero) ((keep _ (by decide)).trans hp) ((keep _ (by decide)).trans hn)
    atRoots atHeap ((keep _ (by decide)).trans atOut) ((keep _ (by decide)).trans atMark)
    outAligned outFits outOutside small heapAligned rootsFits heapBefore
    endAligned endFits (Nat.lt_of_lt_of_le heapBefore (by change heap.toNat ≤ (allocationEnd heap (768#64)).toNat; omega))
    accelAligned accelFits pointerFits accelOutside pointerOutside (allocated.2.2.1.trans code) remaining suffixRun
  rw [run] at agreement
  exact (congrFun agreement.2.2.1 watched).trans (suffix.trans (congrFun allocated.2.1 watched))

#print axioms progressiveRoots_returned_memory
end InitECandidate.Runtime
