import InitECandidate.Runtime.MerkleSizeMemory
import InitECandidate.Runtime.MerklePositiveBound
import InitECandidate.Runtime.HeapMarkCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxHeartbeats 2000000

theorem merkleMark_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator buf zeroHashes initial target out n input watched : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word buf)))
    (heapBound : buf.toNat ≤ 33806089496)
    (atIndex : state.locals.lookup (ofString "dn") = some (.val (.word initial)))
    (atTarget : state.locals.lookup (ofString "target") = some (.val (.word target)))
    (atN : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (atInput : state.locals.lookup (ofString "p") = some (.val (.word input)))
    (lengths : MerkleChunkLengths n ((1#64) <<< initial.toNat))
    (depthBound : initial.toNat ≤ 27)
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (outAligned : out.toNat % 8 = 0) (outFits : out.toNat + 32 ≤ 33806089496)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (small : initial.toNat ≤ target.toNat) (limit : target.toNat ≤ 63)
    (aligned : buf.toNat % 8 = 0)
    (before : watched.toNat < buf.toNat) (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode)
    (budget : 1 + (2 + (merkleMemoryCallCost + (merkleMemoryCallCost + (merkleInputTreeCost + merklePaddingCost + 16)))) ≤ state.clock)
    (run : evaluateHOLFiniteState state (merkleizeAt 4) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  obtain ⟨marked,_,clock,memory,globals,locals,installed,_,_,declaration⟩ :=
    evaluate_heapMark_call_and_declaration state buf code heap (by omega)
  rw [source_merkleMark,declaration] at run
  let next := setVarHOLFinite (ofString "mark") (.val (.word buf)) marked
  change (let output := evaluateHOLFiniteState next (merkleizeAt 5);
    (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "mark",state.locals.lookup (ofString "mark"))})) =
      (some (.returned value),post) at run
  cases tailRun : evaluateHOLFiniteState next (merkleizeAt 5) with
  | mk result inner =>
    rw [tailRun] at run
    obtain ⟨resultEq,postEq⟩ := Prod.mk.inj run
    change result = some (.returned value) at resultEq
    subst result
    have keep (key : MlS) (different : key ≠ ofString "mark") : next.locals.lookup key = state.locals.lookup key := by
      simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
    have frame := merkleSize_suffix_returned_memory next inner pointer accelerator buf zeroHashes initial target out buf n input watched value
      (by change marked.globals.lookup _ = _; rw [globals]; exact atPointer)
      (by change marked.globals.lookup _ = _; rw [globals]; exact atAccel)
      (by change marked.globals.lookup _ = _; rw [globals]; exact atZero)
      (by change marked.globals.lookup _ = _; rw [globals]; exact heap) heapBound
      ((keep _ (by decide)).trans atIndex) ((keep _ (by decide)).trans atTarget)
      ((keep _ (by decide)).trans atN) ((keep _ (by decide)).trans atInput) lengths depthBound
      ((keep _ (by decide)).trans atOut)
      (by simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      outAligned outFits outOutside small limit aligned before accelAligned accelFits pointerFits accelOutside pointerOutside
      (by exact installed.trans code) (by change _ ≤ marked.clock; omega) tailRun
    rw [← postEq]
    exact frame.trans (congrFun memory watched)

#print axioms merkleMark_suffix_returned_memory
end InitECandidate.Runtime
