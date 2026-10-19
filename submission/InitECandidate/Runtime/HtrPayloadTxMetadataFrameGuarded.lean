import InitECandidate.Runtime.HtrPayloadTxBlockMemoryGuarded
import InitECandidate.Runtime.RlpSliceRecordFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrPayload_tx_block_preserves_metadata_guarded (pointer accelerator zeroHashes chunk array roots heap input inputLength count payload chunks mark index valuePointer valueLength : BitVec 64)
    (small : inputLength.toNat ≤ 134217712) (countBound : count.toNat ≤ 134217712)
    (arrayRoots : array.toNat + count.toNat * 16 ≤ roots.toNat)
    (arrayHeap : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (rootsAligned : roots.toNat % 8 = 0) (rootsFits : roots.toNat + count.toNat * 32 ≤ 33806089496)
    (chunkAligned : chunk.toNat % 8 = 0) (chunkFits : count ≠ 0 → chunk.toNat + 32 ≤ array.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : count ≠ 0 → accelerator.toNat + 96 ≤ array.toNat) (pointerFits : count ≠ 0 → pointer.toNat + 64 ≤ array.toNat)
    (payloadRoots : payload.toNat + 72 < roots.toNat) (payloadHeap : payload.toNat + 72 < heap.toNat)
    (chunkPayload : chunk.toNat + 32 ≤ payload.toNat)
    (accelPayload : accelerator.toNat + 96 ≤ payload.toNat) (pointerPayload : pointer.toNat + 64 ≤ payload.toNat)
    {F : Type} (state post : PanSemStateFiniteExact 64 F) (rank : Nat)
    (chunksLocal : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (markLocal : state.locals.lookup (ofString "m2") = some (.val (.word mark)))
    (chunksAligned : chunks.toNat % 8 = 0) (chunksFits : chunks.toNat + 608 ≤ 33806089496)
    (payloadChunks : payload.toNat + 72 < chunks.toNat)
    (code : state.code = originalRuntimeCode)
    (valid : HtrPayloadTxState pointer accelerator zeroHashes chunk array roots heap input inputLength count state rank)
    (entry : RlpSliceEntry state payload index valuePointer valueLength) (indexBound : index.toNat ≤ 4)
    (budget : rank * (htrPbytesBodyCost + 2) + (htrPlistChunksCost + 2) ≤ state.clock)
    (run : evaluateHOLFiniteState state htrPayloadTxBlock = (none,post)) :
    RlpSliceEntry post payload index valuePointer valueLength := by
  have metadata := evaluateHOLFiniteState_metadata state htrPayloadTxBlock
  rw [run] at metadata
  apply entry.after_record_frame state post payload index valuePointer valueLength indexBound (by omega) metadata.2.1
  intro watched lo hi
  exact htrPayload_tx_block_normal_memory_guarded pointer accelerator zeroHashes chunk array roots heap input inputLength count watched chunks mark
    small countBound arrayRoots arrayHeap rootsAligned rootsFits chunkAligned chunkFits heapAligned heapFits accelAligned accelFits pointerFits
    (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) state post rank chunksLocal markLocal
    chunksAligned chunksFits (by omega) code valid budget run

#print axioms htrPayload_tx_block_preserves_metadata_guarded
end InitECandidate.Runtime
