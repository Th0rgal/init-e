import InitECandidate.Runtime.HtrPayloadTxLoopMemory
import InitECandidate.Runtime.HtrPayloadTxHashMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrPayload_tx_block_normal_memory (pointer accelerator zeroHashes chunk array roots heap input inputLength count watched chunks mark : BitVec 64)
    (small : inputLength.toNat ≤ 134217712) (countBound : count.toNat ≤ 134217712)
    (arrayRoots : array.toNat + count.toNat * 16 ≤ roots.toNat)
    (arrayHeap : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (rootsAligned : roots.toNat % 8 = 0) (rootsFits : roots.toNat + count.toNat * 32 ≤ 33806089496)
    (chunkAligned : chunk.toNat % 8 = 0) (chunkFits : chunk.toNat + 32 ≤ array.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ array.toNat) (pointerFits : pointer.toNat + 64 ≤ array.toNat)
    (rootsBefore : watched.toNat < roots.toNat) (heapBefore : watched.toNat < heap.toNat)
    (chunkOutside : watched.toNat < chunk.toNat ∨ chunk.toNat + 32 ≤ watched.toNat)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    {F : Type} (state post : PanSemStateFiniteExact 64 F) (rank : Nat)
    (chunksLocal : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (markLocal : state.locals.lookup (ofString "m2") = some (.val (.word mark)))
    (chunksAligned : chunks.toNat % 8 = 0) (chunksFits : chunks.toNat + 608 ≤ 33806089496)
    (chunksBefore : watched.toNat < chunks.toNat)
    (code : state.code = originalRuntimeCode)
    (valid : HtrPayloadTxState pointer accelerator zeroHashes chunk array roots heap input inputLength count state rank)
    (budget : rank * (htrPbytesBodyCost + 2) + (htrPlistChunksCost + 2) ≤ state.clock)
    (run : evaluateHOLFiniteState state htrPayloadTxBlock = (none,post)) :
    post.memory watched = state.memory watched := by
  obtain ⟨middle,normal,tail⟩ := seq_normal_parts (by exact run)
  have ranked := htrPayload_tx_loop_ranked pointer accelerator zeroHashes chunk array roots heap input inputLength count
    small countBound arrayRoots arrayHeap rootsAligned rootsFits chunkAligned chunkFits heapAligned heapFits
    accelAligned accelFits pointerFits rank state code valid (by omega)
  rw [normal] at ranked
  obtain ⟨nextRank,nextValid,nextCode,_⟩ := ranked.2.2.2 rfl
  have loopFrame := htrPayload_tx_loop_normal_memory pointer accelerator zeroHashes chunk array roots heap input inputLength count watched
    small countBound arrayRoots arrayHeap rootsAligned rootsFits chunkAligned chunkFits heapAligned heapFits accelAligned accelFits pointerFits
    rootsBefore heapBefore chunkOutside accelOutside pointerOutside state middle rank code valid (by omega) normal
  have keep (key : MlS) (different : key ≠ ofString "i") : middle.locals.lookup key = state.locals.lookup key :=
    htrPayload_tx_loop_local_frame state middle key different normal
  have enough : htrPlistChunksCost + 1 ≤ middle.clock := by
    have spent : state.clock ≤ middle.clock + rank * (htrPbytesBodyCost + 2) := ranked.1
    omega
  have frame := htrPayload_tx_hash_release_normal_memory middle post pointer accelerator zeroHashes chunk
    roots count chunks heap mark watched nextValid.rootsLocal nextValid.countLocal
    ((keep _ (by decide)).trans chunksLocal) ((keep _ (by decide)).trans markLocal)
    nextValid.pointerGlobal nextValid.accelGlobal nextValid.chunkGlobal nextValid.zeroGlobal nextValid.heapGlobal
    chunksAligned chunksFits chunksBefore countBound chunkAligned (by omega) chunkOutside heapAligned heapFits heapBefore
    accelAligned (by omega) (by omega) accelOutside pointerOutside (nextCode.trans code) enough tail
  exact frame.trans loopFrame

#print axioms htrPayload_tx_block_normal_memory
end InitECandidate.Runtime
