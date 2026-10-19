import InitECandidate.Runtime.MerkleDepthMemory
import InitECandidate.Runtime.MerkleLevelsMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem merkleTree_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator buf zeroHashes initial target out mark cur watched : BitVec 64) (chunks : Nat) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (atBuf : state.locals.lookup (ofString "buf") = some (.val (.word buf)))
    (atIndex : state.locals.lookup (ofString "dn") = some (.val (.word initial)))
    (atTarget : state.locals.lookup (ofString "target") = some (.val (.word target)))
    (atCur : state.locals.lookup (ofString "cur") = some (.val (.word cur)))
    (countBound : cur.toNat ≤ chunks) (positive : 0 < chunks) (chunksBound : chunks ≤ 134217728)
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (outAligned : out.toNat % 8 = 0) (outFits : out.toNat + 32 ≤ 33806089496)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (small : initial.toNat ≤ target.toNat) (limit : target.toNat ≤ 63)
    (aligned : buf.toNat % 8 = 0) (fits : buf.toNat + chunks * 32 ≤ 33806089496)
    (before : watched.toNat < buf.toNat) (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode)
    (budget : merkleInputTreeCost + merklePaddingCost + 16 ≤ state.clock)
    (run : evaluateHOLFiniteState state (merkleizeAt 10) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  rw [source_merkleLevels] at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile (.while merkleLevelsCondition merkleLevelBody) (by decide) state v) run
  have actualCost : cur.toNat * (chunks * 137 + 1) ≤ merkleInputTreeCost := by
    unfold merkleInputTreeCost
    apply Nat.mul_le_mul
    · omega
    · omega
  have frame := merkleLevels_loop_normal_memory state middle pointer accelerator buf cur watched chunks
    atPointer atAccel atBuf atCur countBound aligned fits before accelAligned accelFits pointerFits
    accelOutside pointerOutside code (by omega) normal
  have clocks := runBounded_merkleInputLevels state cur atCur (by omega) code (by omega)
  have globals := originalGlobalsFrame_while merkleLevelsCondition merkleLevelBody merkleLevel_body_globals state code
  have meta' := evaluateHOLFiniteState_metadata state (.while merkleLevelsCondition merkleLevelBody)
  unfold RunBounded at clocks
  rw [normal] at globals clocks meta'
  have keep (key : MlS) (supported : avoidsLocal key (.while merkleLevelsCondition merkleLevelBody) = true) :
      middle.locals.lookup key = state.locals.lookup key := by
    have locals := evaluate_avoidsLocal_flowing key (.while merkleLevelsCondition merkleLevelBody) supported state
      (by rw [normal]; exact Or.inl rfl)
    simpa only [normal] using locals
  have suffix := merkleDepth_suffix_returned_memory middle post pointer accelerator buf zeroHashes initial target out mark watched value
    (by rw [globals]; exact atPointer) (by rw [globals]; exact atAccel) (by rw [globals]; exact atZero)
    ((keep _ (by decide)).trans atBuf) ((keep _ (by decide)).trans atIndex) ((keep _ (by decide)).trans atTarget)
    ((keep _ (by decide)).trans atOut) ((keep _ (by decide)).trans atMark)
    outAligned outFits outOutside small limit aligned (by omega) before accelAligned accelFits pointerFits
    accelOutside pointerOutside (meta'.1.trans code) (by dsimp only at clocks; omega) tail
  exact suffix.trans frame

#print axioms merkleTree_suffix_returned_memory
end InitECandidate.Runtime
