import InitECandidate.Runtime.HtrPayloadTxBlockBound
import InitECandidate.Runtime.HtrPlistChunksMemory
import InitECandidate.Runtime.HeapReleaseMemory
import InitECandidate.Runtime.HtabDelBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrPayload_tx_hash_release_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator zeroHashes chunk roots count chunks heap mark watched : BitVec 64)
    (rootsLocal : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (countLocal : state.locals.lookup (ofString "ntx") = some (.val (.word count)))
    (chunksLocal : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (markLocal : state.locals.lookup (ofString "m2") = some (.val (.word mark)))
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atChunk : state.globals.lookup (ofString "ssz_len_chunk") = some (.val (.word chunk)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (chunksAligned : chunks.toNat % 8 = 0) (chunksFits : chunks.toNat + 608 ≤ 33806089496)
    (chunksBefore : watched.toNat < chunks.toNat)
    (countBound : count.toNat ≤ 134217712)
    (chunkAligned : chunk.toNat % 8 = 0) (chunkFits : chunk.toNat + 32 ≤ 33806089496)
    (chunkOutside : watched.toNat < chunk.toNat ∨ chunk.toNat + 32 ≤ watched.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496) (heapBefore : watched.toNat < heap.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : htrPlistChunksCost + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.seq htrPayloadTxHashCall htrPayloadTxRelease) = (none,post)) :
    post.memory watched = state.memory watched := by
  obtain ⟨middle,normal,release⟩ := seq_normal_parts run
  have natural : (chunks + (416#64)).toNat = chunks.toNat + 416 := by
    apply BitVec.toNat_add_of_lt
    change chunks.toNat + 416 < 2 ^ 64
    omega
  have aligned : (chunks + (416#64)).toNat % 8 = 0 := by
    rw [natural,Nat.add_mod,chunksAligned]
  have frame := htrPlistChunks_call_normal_memory state middle htrPayloadTxHashArguments
    pointer accelerator zeroHashes chunk roots count count heap (chunks + (416#64)) watched
    (htrPayload_tx_hash_arguments state roots count chunks rootsLocal countLocal chunksLocal)
    atPointer atAccel atChunk chunkAligned chunkFits chunkOutside atZero atHeap
    aligned (by rw [natural]; omega) (Or.inl (by rw [natural]; omega)) countBound
    heapAligned heapFits heapBefore accelAligned accelFits pointerFits accelOutside pointerOutside code budget normal
  have keepMark : middle.locals.lookup (ofString "m2") = some (.val (.word mark)) := by
    have keep := evaluate_avoidsLocal_flowing (ofString "m2") htrPayloadTxHashCall rfl state
      (by rw [normal]; exact Or.inl rfl)
    rw [normal] at keep
    exact keep.trans markLocal
  have metadata := evaluateHOLFiniteState_metadata state htrPayloadTxHashCall
  rw [normal] at metadata
  have released := heapRelease_call_normal_memory middle post (.var .local (ofString "m2")) mark
    (metadata.1.trans code) (by simp [evalListHOLExact,evalHOLExact,keepMark]) release
  exact (congrFun released watched).trans frame

#print axioms htrPayload_tx_hash_release_normal_memory
end InitECandidate.Runtime
