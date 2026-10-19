import InitECandidate.Runtime.MerkleCopyMemory
import InitECandidate.Runtime.MerkleAllocationBound
import InitECandidate.Runtime.ReachesReturnedContinuation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem merkleAllocation_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator buf zeroHashes initial target out mark cur n input watched : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word buf)))
    (heapBound : buf.toNat ≤ 33806089496)
    (atIndex : state.locals.lookup (ofString "dn") = some (.val (.word initial)))
    (atTarget : state.locals.lookup (ofString "target") = some (.val (.word target)))
    (atCur : state.locals.lookup (ofString "size") = some (.val (.word cur)))
    (atN : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (atInput : state.locals.lookup (ofString "p") = some (.val (.word input)))
    (lengths : MerkleChunkLengths n cur)
    (positive : 0 < cur.toNat)
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (outAligned : out.toNat % 8 = 0) (outFits : out.toNat + 32 ≤ 33806089496)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (small : initial.toNat ≤ target.toNat) (limit : target.toNat ≤ 63)
    (aligned : buf.toNat % 8 = 0)
    (before : watched.toNat < buf.toNat) (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode)
    (budget : 2 + (merkleMemoryCallCost + (merkleMemoryCallCost + (merkleInputTreeCost + merklePaddingCost + 16))) ≤ state.clock)
    (run : evaluateHOLFiniteState state (merkleizeAt 6) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.panop .mul [.var .local (ofString "size"),.const 32]] = some [.val (.word (cur * (32#64)))] := by
    simp [evalListHOLExact,evalHOLExact,atCur,panOpHOL,valueIsWord,valueWord]
  have reached := evaluate_allocation_declaration_reaches state
    (.panop .mul [.var .local (ofString "size"),.const 32]) (ofString "buf") buf (cur * (32#64))
    (merkleizeAt 7) args code heap heapBound (by omega)
  rw [← source_merkleAllocation] at reached
  obtain ⟨ready,allocated,spent,_,agreement,returned⟩ := reaches_returned_continuation state
    (merkleizeAt 6) (merkleizeAt 7) _ 2 value reached (by rw [run])
  have keep (key : MlS) (different : key ≠ ofString "buf") : ready.locals.lookup key = state.locals.lookup key := by
    rw [allocated.1]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have globalKeep (key : MlS) (different : key ≠ ofString "heap_ptr") : ready.globals.lookup key = state.globals.lookup key := by
    rw [allocated.2.2.2.2.1]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have atBuffer : ready.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
    rw [allocated.1]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have bufferFits : buf.toNat + cur.toNat * 32 ≤ 33806089496 := by
    have cap := allocated.2.2.2.2.2.1
    have covers := allocated.2.2.2.2.2.2.1
    rw [lengths.2.2.1] at covers
    omega
  have suffixRun : evaluateHOLFiniteState ready (merkleizeAt 7) =
      (some (.returned value),(evaluateHOLFiniteState ready (merkleizeAt 7)).2) := Prod.ext returned rfl
  have suffix := merkleCopy_suffix_returned_memory ready _ pointer accelerator buf zeroHashes initial target out mark cur n input watched cur.toNat value
    ((globalKeep _ (by decide)).trans atPointer) ((globalKeep _ (by decide)).trans atAccel)
    ((globalKeep _ (by decide)).trans atZero) atBuffer
    ((keep _ (by decide)).trans atIndex) ((keep _ (by decide)).trans atTarget)
    ((keep _ (by decide)).trans atCur) ((keep _ (by decide)).trans atN) ((keep _ (by decide)).trans atInput)
    lengths (le_refl _) positive lengths.2.1
    ((keep _ (by decide)).trans atOut) ((keep _ (by decide)).trans atMark)
    outAligned outFits outOutside small limit aligned bufferFits before accelAligned accelFits pointerFits
    accelOutside pointerOutside (allocated.2.2.1.trans code) (by omega) suffixRun
  rw [run] at agreement
  exact (congrFun agreement.2.2.1 watched).trans (suffix.trans (congrFun allocated.2.1 watched))

#print axioms merkleAllocation_suffix_returned_memory
end InitECandidate.Runtime
