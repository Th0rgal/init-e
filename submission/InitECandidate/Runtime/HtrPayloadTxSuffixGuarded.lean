import InitECandidate.Runtime.HtrPayloadTxSuffixBound
import InitECandidate.Runtime.HtrPayloadTxBlockGuarded
import InitECandidate.Runtime.HtrPayloadTxMetadataFrameGuarded
import InitECandidate.Runtime.HtrPayloadTxBlockCursorGuarded
import InitECandidate.Runtime.HtrPayloadWithdrawalMetadataSuffixBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem runBounded_htrPayload_tx_suffix_guarded (pointer accelerator zeroHashes chunk array roots heap input inputLength count payload chunks mark withdrawalArray withdrawalCount requests requestLength raw out : BitVec 64)
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
    {F : Type} (state : PanSemStateFiniteExact 64 F) (rank : Nat)
    (chunksLocal : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (markLocal : state.locals.lookup (ofString "m2") = some (.val (.word mark)))
    (chunksAligned : chunks.toNat % 8 = 0) (chunksFits : chunks.toNat + 608 ≤ 33806089496)
    (payloadChunks : payload.toNat + 72 < chunks.toNat)
    (code : state.code = originalRuntimeCode)
    (valid : HtrPayloadTxState pointer accelerator zeroHashes chunk array roots heap input inputLength count state rank)
    (rawLocal : state.locals.lookup (ofString "raw") = some (.val (.word raw)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (payloadLocal : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (markAligned : mark.toNat % 8 = 0) (markBound : mark.toNat ≤ 33806089496)
    (payloadMark : payload.toNat + 72 < mark.toNat)
    (withdrawals : RlpSliceEntry state payload (3#64) withdrawalArray withdrawalCount)
    (withdrawalBound : withdrawalCount.toNat ≤ 134217712)
    (requestEntry : RlpSliceEntry state payload (4#64) requests requestLength)
    (requestBound : requestLength.toNat ≤ 134217712)
    (budget : (rank * (htrPbytesBodyCost + 2) + (htrPlistChunksCost + 2)) + htrPayloadWithdrawalTotalCost withdrawalCount ≤ state.clock) :
    RunBounded state (htrPayloadAt 21)
      ((rank * (htrPbytesBodyCost + 2) + (htrPlistChunksCost + 2)) + htrPayloadWithdrawalTotalCost withdrawalCount) := by
  unfold RunBounded
  rw [evaluate_htrPayload_tx_block_source]
  change RunBounded state (.seq htrPayloadTxBlock (htrPayloadAt 24)) _
  have first := runBounded_htrPayload_tx_block_guarded pointer accelerator zeroHashes chunk array roots heap input inputLength count
    small countBound arrayRoots arrayHeap rootsAligned rootsFits chunkAligned chunkFits heapAligned heapFits
    accelAligned accelFits pointerFits state rank chunks code valid chunksLocal (by omega)
  exact RunBounded.seq first budget (by
    intro next normal nextCode remaining
    have keep (key : MlS) (different : key ≠ ofString "i") : next.locals.lookup key = state.locals.lookup key :=
      htrPayload_tx_block_local_frame state next key different normal
    have globals := htrPayload_tx_block_normal_globals state next mark markLocal code normal
    have nonHeap (key : MlS) (different : key ≠ ofString "heap_ptr") :
        next.globals.lookup key = state.globals.lookup key := by
      rw [globals]
      simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
    have nextHeap := htrPayload_tx_block_normal_heap state next mark markLocal code normal
    have cursor := htrPayload_tx_block_normal_cursor_guarded pointer accelerator zeroHashes chunk array roots heap input inputLength count
      small countBound arrayRoots arrayHeap rootsAligned rootsFits chunkAligned chunkFits heapAligned heapFits
      accelAligned accelFits pointerFits state next rank code valid (by omega) normal
    have transfer (index p n : BitVec 64) (entry : RlpSliceEntry state payload index p n) (inside : index.toNat ≤ 4) :
        RlpSliceEntry next payload index p n :=
      htrPayload_tx_block_preserves_metadata_guarded pointer accelerator zeroHashes chunk array roots heap input inputLength count
        payload chunks mark index p n small countBound arrayRoots arrayHeap rootsAligned rootsFits chunkAligned chunkFits
        heapAligned heapFits accelAligned accelFits pointerFits payloadRoots payloadHeap chunkPayload accelPayload pointerPayload
        state next rank chunksLocal markLocal chunksAligned chunksFits payloadChunks code valid entry inside (by omega) normal
    exact runBounded_htrPayload_withdrawal_metadata_suffix next pointer accelerator zeroHashes chunk withdrawalArray mark withdrawalCount
      chunks mark payload requests requestLength raw out count
      ((keep _ (by decide)).trans rawLocal) ((keep _ (by decide)).trans outLocal) ((keep _ (by decide)).trans payloadLocal)
      requestBound markBound ((keep _ (by decide)).trans chunksLocal) ((keep _ (by decide)).trans markLocal)
      chunksAligned chunksFits payloadChunks chunkAligned chunkPayload ((nonHeap _ (by decide)).trans valid.chunkGlobal)
      withdrawalBound markAligned markBound payloadMark accelAligned accelPayload pointerPayload (nextCode.trans code)
      (transfer (3#64) withdrawalArray withdrawalCount withdrawals (by decide)) cursor nextHeap
      ((nonHeap _ (by decide)).trans valid.pointerGlobal) ((nonHeap _ (by decide)).trans valid.accelGlobal)
      ((nonHeap _ (by decide)).trans valid.zeroGlobal) (transfer (4#64) requests requestLength requestEntry (by decide)) remaining)

#print axioms runBounded_htrPayload_tx_suffix_guarded
end InitECandidate.Runtime
