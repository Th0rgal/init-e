import InitECandidate.Runtime.MerkleZeroMemory
import InitECandidate.Runtime.MemcpyCallMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem merkleCopy_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator buf zeroHashes initial target out mark cur n input watched : BitVec 64) (chunks : Nat) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (atBuf : state.locals.lookup (ofString "buf") = some (.val (.word buf)))
    (atIndex : state.locals.lookup (ofString "dn") = some (.val (.word initial)))
    (atTarget : state.locals.lookup (ofString "target") = some (.val (.word target)))
    (atCur : state.locals.lookup (ofString "size") = some (.val (.word cur)))
    (atN : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (atInput : state.locals.lookup (ofString "p") = some (.val (.word input)))
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
    (budget : merkleMemoryCallCost + (merkleMemoryCallCost + (merkleInputTreeCost + merklePaddingCost + 16)) ≤ state.clock)
    (run : evaluateHOLFiniteState state (merkleizeAt 7) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  obtain ⟨covers,sizeBound,totalNat,copyNat,zeroNat,totalBound,copyBound,zeroBound,partition⟩ := lengths
  have copyFits : buf.toNat + (n * (32#64)).toNat ≤ 33806089496 := by rw [copyNat]; omega
  have separate := memcpy_interval_separate buf (n * (32#64)) watched aligned copyFits (Or.inl before)
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) merkleCopyArguments =
      some [.val (.word buf),.val (.word input),.val (.word (n * (32#64)))] := by
    simp [merkleCopyArguments,evalListHOLExact,evalHOLExact,atBuf,atN,atInput,
      wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]
  rw [source_merkleCopy] at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return state (ofString "memcpy") merkleCopyArguments v) run
  have cost := merkle_memory_call_cost_le (n * (32#64)) copyBound
  have frame := memcpy_call_normal_memory state middle merkleCopyArguments buf input (n * (32#64)) watched args code
    (fun offset inside => (separate offset inside).1) (fun offset inside => (separate offset inside).2)
    (by omega) (by omega) normal
  have globals := memcpy_call_globals_frame merkleCopyArguments state code
  have meta' := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "memcpy") merkleCopyArguments)
  have clocks := evaluate_memcpy_call_bounded state merkleCopyArguments buf input (n * (32#64)) args code (by omega) (by omega)
  rw [normal] at globals meta' clocks
  have keep (key : MlS) : middle.locals.lookup key = state.locals.lookup key := by
    have locals := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "memcpy") merkleCopyArguments)
      rfl state (by rw [normal]; exact Or.inl rfl)
    simpa only [normal] using locals
  have suffix := merkleZero_suffix_returned_memory middle post pointer accelerator buf zeroHashes initial target out mark cur n watched chunks value
    (by rw [globals]; exact atPointer) (by rw [globals]; exact atAccel) (by rw [globals]; exact atZero)
    ((keep _).trans atBuf) ((keep _).trans atIndex) ((keep _).trans atTarget) ((keep _).trans atCur) ((keep _).trans atN)
    ⟨covers,sizeBound,totalNat,copyNat,zeroNat,totalBound,copyBound,zeroBound,partition⟩ countBound positive chunksBound
    ((keep _).trans atOut) ((keep _).trans atMark)
    outAligned outFits outOutside small limit aligned fits before accelAligned accelFits pointerFits
    accelOutside pointerOutside (meta'.1.trans code) (by dsimp only at clocks; omega) tail
  exact suffix.trans frame

#print axioms merkleCopy_suffix_returned_memory
end InitECandidate.Runtime
