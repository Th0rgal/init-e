import InitECandidate.Runtime.MerklePaddingLoopMemory
import InitECandidate.Runtime.MerkleFinishMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem merklePadding_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator buf zeroHashes initial target out mark watched : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (atBuf : state.locals.lookup (ofString "buf") = some (.val (.word buf)))
    (atIndex : state.locals.lookup (ofString "d") = some (.val (.word initial)))
    (atTarget : state.locals.lookup (ofString "target") = some (.val (.word target)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (outAligned : out.toNat % 8 = 0) (outFits : out.toNat + 32 ≤ 33806089496)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (small : initial.toNat ≤ target.toNat) (limit : target.toNat ≤ 63)
    (aligned : buf.toNat % 8 = 0) (fits : buf.toNat + 32 ≤ 33806089496)
    (before : watched.toNat < buf.toNat) (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode)
    (budget : merklePaddingCost + 16 ≤ state.clock)
    (run : evaluateHOLFiniteState state (merkleizeAt 12) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  rw [source_merklePadding] at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile merklePaddingLoop (by decide) state v) run
  have frame := merklePadding_loop_normal_memory state middle pointer accelerator buf zeroHashes initial target watched
    atPointer atAccel atZero atBuf atIndex atTarget small limit aligned fits before accelAligned accelFits pointerFits
    accelOutside pointerOutside code (by unfold merklePaddingCost at budget; omega) normal
  have clocks := runBounded_merklePadding state initial target atIndex atTarget (by omega) limit code (by omega)
  have meta' := evaluateHOLFiniteState_metadata state merklePaddingLoop
  unfold RunBounded at clocks
  rw [normal] at clocks meta'
  have keep (key : MlS) (supported : avoidsLocal key merklePaddingLoop = true) :
      middle.locals.lookup key = state.locals.lookup key := by
    have locals := evaluate_avoidsLocal_flowing key merklePaddingLoop supported state
      (by rw [normal]; exact Or.inl rfl)
    simpa only [normal] using locals
  have suffix := merkleFinish_returned_memory middle post buf out mark watched value
    ((keep _ (by decide)).trans atBuf) ((keep _ (by decide)).trans atOut) ((keep _ (by decide)).trans atMark)
    outAligned outFits outOutside (meta'.1.trans code) (by dsimp only at clocks; omega) tail
  exact suffix.trans frame

#print axioms merklePadding_suffix_returned_memory
end InitECandidate.Runtime
