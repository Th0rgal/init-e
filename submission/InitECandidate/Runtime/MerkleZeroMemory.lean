import InitECandidate.Runtime.MerkleCounterMemory
import InitECandidate.Runtime.MerkleMemoryBound
import InitECandidate.Runtime.MemzeroSeparatedMemory
import InitECandidate.Runtime.SubintervalMemorySeparation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem merkleZero_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator buf zeroHashes initial target out mark cur n watched : BitVec 64) (chunks : Nat) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (atBuf : state.locals.lookup (ofString "buf") = some (.val (.word buf)))
    (atIndex : state.locals.lookup (ofString "dn") = some (.val (.word initial)))
    (atTarget : state.locals.lookup (ofString "target") = some (.val (.word target)))
    (atCur : state.locals.lookup (ofString "size") = some (.val (.word cur)))
    (atN : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (lengths : MerkleChunkLengths n cur)
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
    (budget : merkleMemoryCallCost + (merkleInputTreeCost + merklePaddingCost + 16) ≤ state.clock)
    (run : evaluateHOLFiniteState state (merkleizeAt 8) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  obtain ⟨covers,sizeBound,totalNat,copyNat,zeroNat,totalBound,copyBound,zeroBound,partition⟩ := lengths
  have totalFits : buf.toNat + (cur * (32#64)).toNat ≤ 33806089496 := by rw [totalNat]; omega
  have geometry := aligned_subinterval_memory_separate buf (cur * (32#64)) (n * (32#64))
    ((cur - n) * (32#64)) watched aligned totalFits (by omega) (Or.inl before)
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) merkleZeroArguments =
      some [.val (.word (buf + n * (32#64))),.val (.word ((cur - n) * (32#64)))] := by
    simp [merkleZeroArguments,evalListHOLExact,evalHOLExact,atBuf,atN,atCur,
      wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]
  rw [source_merkleZero] at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return state (ofString "memzero") merkleZeroArguments v) run
  obtain ⟨frame,locals⟩ := memzero_call_normal_separated_memory state middle merkleZeroArguments (buf + n * (32#64))
    ((cur - n) * (32#64)) watched args code geometry.1 geometry.2 normal
  have globals := memzero_call_globals_frame merkleZeroArguments state code
  have meta' := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "memzero") merkleZeroArguments)
  have cost := merkle_memory_call_cost_le ((cur - n) * (32#64)) zeroBound
  have clocks := evaluate_memzero_call_bounded state merkleZeroArguments (buf + n * (32#64)) ((cur - n) * (32#64))
    args code (by omega) (by omega)
  rw [normal] at globals meta' clocks
  have suffix := merkleCounter_suffix_returned_memory middle post pointer accelerator buf zeroHashes initial target out mark cur watched chunks value
    (by rw [globals]; exact atPointer) (by rw [globals]; exact atAccel) (by rw [globals]; exact atZero)
    (by rw [locals]; exact atBuf) (by rw [locals]; exact atIndex) (by rw [locals]; exact atTarget)
    (by rw [locals]; exact atCur) countBound positive chunksBound
    (by rw [locals]; exact atOut) (by rw [locals]; exact atMark)
    outAligned outFits outOutside small limit aligned fits before accelAligned accelFits pointerFits
    accelOutside pointerOutside (meta'.1.trans code) (by dsimp only at clocks; omega) tail
  exact suffix.trans frame

#print axioms merkleZero_suffix_returned_memory
end InitECandidate.Runtime
