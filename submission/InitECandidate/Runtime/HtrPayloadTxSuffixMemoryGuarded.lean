import InitECandidate.Runtime.HtrPayloadTxSuffixMemory
import InitECandidate.Runtime.HtrPayloadTxSuffixGuarded
import InitECandidate.Runtime.HtrPayloadTxBlockGuarded
import InitECandidate.Runtime.HtrPayloadTxBlockMemoryGuarded
import InitECandidate.Runtime.HtrPayloadTxBlockCursorGuarded
import InitECandidate.Runtime.HtrPayloadTxMetadataFrameGuarded
import InitECandidate.Runtime.HtrPayloadWithdrawalMetadataMemory
import InitECandidate.Runtime.HtrPayloadTxSuffixBound
import InitECandidate.Runtime.HtrPayloadTxBlockMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- The real transaction block, inner release and full withdrawal/final suffix
preserve the watched word while transferring decoded metadata and the cursor. -/
theorem htrPayload_tx_suffix_returned_memory_guarded (pointer accelerator zeroHashes chunk array roots heap input inputLength count payload chunks mark withdrawalArray withdrawalCount requests requestLength raw out outerMark watched : BitVec 64)
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
    {F : Type} (state post : PanSemStateFiniteExact 64 F) (rank : Nat) (value : ValueHOL 64)
    (layout : ListHashMemoryLayout state pointer accelerator zeroHashes chunk heap out watched)
    (outerLocal : state.locals.lookup (ofString "mark") = some (.val (.word outerMark)))
    (watchedRoots : watched.toNat < roots.toNat) (watchedChunks : watched.toNat < chunks.toNat)
    (watchedMark : watched.toNat < mark.toNat)
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
    (budget : (rank * (htrPbytesBodyCost + 2) + (htrPlistChunksCost + 2)) + htrPayloadWithdrawalTotalCost withdrawalCount ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrPayloadAt 21) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  rw [evaluate_htrPayload_tx_block_source] at run
  obtain ⟨next,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile _ (by decide) state v) run
  let blockCost := rank * (htrPbytesBodyCost + 2) + (htrPlistChunksCost + 2)
  have enough : blockCost ≤ state.clock :=
    (Nat.le_add_right blockCost (htrPayloadWithdrawalTotalCost withdrawalCount)).trans budget
  have frame := htrPayload_tx_block_normal_memory_guarded pointer accelerator zeroHashes chunk array roots heap input inputLength count watched chunks mark
    small countBound arrayRoots arrayHeap rootsAligned rootsFits chunkAligned chunkFits heapAligned heapFits accelAligned accelFits pointerFits
    layout.chunkFits layout.accelFits layout.shaFits watchedRoots layout.heapBefore layout.chunkOutside layout.accelOutside layout.shaOutside state next rank chunksLocal markLocal
    chunksAligned chunksFits watchedChunks code valid enough normal
  have keep (key : MlS) (different : key ≠ ofString "i") : next.locals.lookup key = state.locals.lookup key :=
    htrPayload_tx_block_local_frame state next key different normal
  have globals := htrPayload_tx_block_normal_globals state next mark markLocal code normal
  have metadata := evaluateHOLFiniteState_metadata state htrPayloadTxBlock
  have bounded := runBounded_htrPayload_tx_block_guarded pointer accelerator zeroHashes chunk array roots heap input inputLength count
    small countBound arrayRoots arrayHeap rootsAligned rootsFits chunkAligned chunkFits heapAligned heapFits accelAligned accelFits pointerFits
    state rank chunks code valid chunksLocal enough
  unfold RunBounded at bounded
  rw [normal] at metadata bounded
  have cursorEnough : rank * (htrPbytesBodyCost + 2) ≤ state.clock :=
    (Nat.le_add_right (rank * (htrPbytesBodyCost + 2)) (htrPlistChunksCost + 2)).trans enough
  have cursor := htrPayload_tx_block_normal_cursor_guarded pointer accelerator zeroHashes chunk array roots heap input inputLength count
    small countBound arrayRoots arrayHeap rootsAligned rootsFits chunkAligned chunkFits heapAligned heapFits accelAligned accelFits pointerFits
    state next rank code valid cursorEnough normal
  have transfer (index p n : BitVec 64) (entry : RlpSliceEntry state payload index p n) (inside : index.toNat ≤ 4) :
      RlpSliceEntry next payload index p n :=
    htrPayload_tx_block_preserves_metadata_guarded pointer accelerator zeroHashes chunk array roots heap input inputLength count
      payload chunks mark index p n small countBound arrayRoots arrayHeap rootsAligned rootsFits chunkAligned chunkFits heapAligned heapFits
      accelAligned accelFits pointerFits payloadRoots payloadHeap chunkPayload accelPayload pointerPayload state next rank chunksLocal markLocal
      chunksAligned chunksFits payloadChunks code valid entry inside enough normal
  have nextLayout := layout.after_heap_restore globals metadata.1 markAligned markBound watchedMark
  have spent : state.clock ≤ next.clock + blockCost := bounded.1
  have remaining : htrPayloadWithdrawalTotalCost withdrawalCount ≤ next.clock := by
    change blockCost + htrPayloadWithdrawalTotalCost withdrawalCount ≤ state.clock at budget
    generalize blockCost = bc at budget spent
    generalize htrPayloadWithdrawalTotalCost withdrawalCount = cost at budget ⊢
    omega
  have suffix := htrPayload_withdrawal_metadata_suffix_returned_memory next post pointer accelerator zeroHashes chunk withdrawalArray mark
    withdrawalCount chunks mark outerMark payload requests requestLength raw out count watched value nextLayout
    ⟨(keep _ (by decide)).trans payloadLocal,(keep _ (by decide)).trans rawLocal,
      (keep _ (by decide)).trans chunksLocal,(keep _ (by decide)).trans outLocal⟩
    ((keep _ (by decide)).trans outerLocal) ((keep _ (by decide)).trans markLocal)
    markAligned markBound watchedMark requestBound withdrawalBound chunksAligned chunksFits payloadChunks watchedChunks payloadMark
    chunkPayload accelPayload pointerPayload (transfer (3#64) withdrawalArray withdrawalCount withdrawals (by decide)) cursor
    (transfer (4#64) requests requestLength requestEntry (by decide)) remaining tail
  exact suffix.trans frame

#print axioms htrPayload_tx_suffix_returned_memory_guarded
end InitECandidate.Runtime
