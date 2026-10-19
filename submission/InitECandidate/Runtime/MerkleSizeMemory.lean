import InitECandidate.Runtime.MerkleAllocationMemory
import InitECandidate.Runtime.PanDecWordResultScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem merkleSize_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator buf zeroHashes initial target out mark n input watched : BitVec 64) (value : ValueHOL 64)
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
    (run : evaluateHOLFiniteState state (merkleizeAt 5) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have legal : ¬ (initial.toNat ≠ 0 ∧ 64 ≤ initial.toNat) := by omega
  have initialized : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.shift .lsl (.const 1) (.var .local (ofString "dn"))) =
      some (.val (.word ((1#64) <<< initial.toNat))) := by
    simp [evalHOLExact,atIndex,wordShiftHOL,legal]
  rw [source_merkleSize_declaration] at run
  obtain ⟨inner,bodyRun,scope⟩ := evaluate_dec_word_result_scope state post (ofString "size")
    _ ((1#64) <<< initial.toNat) (merkleizeAt 6) (some (.returned value)) initialized run
  let entered := setVarHOLFinite (ofString "size") (.val (.word ((1#64) <<< initial.toNat))) state
  have keep (key : MlS) (different : key ≠ ofString "size") : entered.locals.lookup key = state.locals.lookup key := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have positive : 0 < ((1#64) <<< initial.toNat).toNat := by
    rw [shift_one_toNat_of_lt64 initial (by omega)]
    exact Nat.two_pow_pos _
  have frame := merkleAllocation_suffix_returned_memory entered inner pointer accelerator buf zeroHashes initial target out mark
    ((1#64) <<< initial.toNat) n input watched value
    atPointer atAccel atZero heap heapBound ((keep _ (by decide)).trans atIndex) ((keep _ (by decide)).trans atTarget)
    (by simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    ((keep _ (by decide)).trans atN) ((keep _ (by decide)).trans atInput) lengths positive
    ((keep _ (by decide)).trans atOut) ((keep _ (by decide)).trans atMark)
    outAligned outFits outOutside small limit aligned before accelAligned accelFits pointerFits
    accelOutside pointerOutside code budget bodyRun
  rw [scope]
  exact frame

#print axioms merkleSize_suffix_returned_memory
end InitECandidate.Runtime
