import InitECandidate.Runtime.HtrPayloadHeaderCopyMemory
import InitECandidate.Runtime.HtrPayloadTxMetadataMemoryGuarded
import InitECandidate.Runtime.HtrBytesVectorDecodedFrameGuarded
import InitECandidate.Runtime.HtrPayloadTxMetadataMemory
import InitECandidate.Runtime.HtrPayloadHeaderCopySuffixBound
import InitECandidate.Runtime.MemcpyCallMemory
import InitECandidate.Runtime.MemcpyIntervalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- Header suffix memory preservation with all concrete decoded/count/layout premises. -/
def PayloadHeaderSuffixMemory_guarded (index : Nat) (cost : BitVec 64 → BitVec 64 → Nat) : Prop :=
  ∀ (pointer accelerator zeroHashes chunk array heap input inputLength count payload chunks withdrawalArray withdrawalCount requests requestLength raw out blobs blobLength outerMark watched : BitVec 64)
    (small : inputLength.toNat ≤ 134217712) (countBound : count.toNat ≤ 134217712)
    (arrayHeap : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (arrayChunks : array.toNat + count.toNat * 16 ≤ chunks.toNat)
    (chunkAligned : chunk.toNat % 8 = 0) (chunkFits : count ≠ 0 → chunk.toNat + 32 ≤ array.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : count ≠ 0 → accelerator.toNat + 96 ≤ array.toNat) (pointerFits : count ≠ 0 → pointer.toNat + 64 ≤ array.toNat)
    (payloadHeap : payload.toNat + 72 < heap.toNat)
    (chunkPayload : chunk.toNat + 32 ≤ payload.toNat)
    (accelPayload : accelerator.toNat + 96 ≤ payload.toNat) (pointerPayload : pointer.toNat + 64 ≤ payload.toNat)
    {F : Type} (state post : PanSemStateFiniteExact 64 F) (value : ValueHOL 64)
    (layout : ListHashMemoryLayout state pointer accelerator zeroHashes chunk heap out watched)
    (outerLocal : state.locals.lookup (ofString "mark") = some (.val (.word outerMark)))
    (watchedChunks : watched.toNat < chunks.toNat)
    (chunksLocal : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (chunksAligned : chunks.toNat % 8 = 0) (chunksFits : chunks.toNat + 608 ≤ 33806089496)
    (payloadChunks : payload.toNat + 72 < chunks.toNat)
    (code : state.code = originalRuntimeCode)
    (pointerGlobal : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (accelGlobal : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (zeroGlobal : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (chunkGlobal : state.globals.lookup (ofString "ssz_len_chunk") = some (.val (.word chunk)))
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (transactions : RlpSliceEntry state payload (2#64) array count)
    (slices : RlpSliceInputPrefix state array input inputLength count.toNat)
    (rawLocal : state.locals.lookup (ofString "raw") = some (.val (.word raw)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (payloadLocal : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (withdrawals : RlpSliceEntry state payload (3#64) withdrawalArray withdrawalCount)
    (withdrawalBound : withdrawalCount.toNat ≤ 134217712)
    (requestEntry : RlpSliceEntry state payload (4#64) requests requestLength)
    (requestBound : requestLength.toNat ≤ 134217712)
    (blobEntry : RlpSliceEntry state payload (1#64) blobs blobLength)
    (blobBound : blobLength.toNat ≤ 134217712)
    (budget : cost count withdrawalCount ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrPayloadAt index) = (some (.returned value),post)),
    post.memory watched = state.memory watched

theorem payload_header_tx_metadata_memory_guarded : PayloadHeaderSuffixMemory_guarded 16 htrPayloadTxMetadataCost := by
  intro pointer accelerator zeroHashes chunk array heap input inputLength count payload chunks withdrawalArray withdrawalCount
    requests requestLength raw out blobs blobLength outerMark watched small countBound arrayHeap arrayChunks chunkAligned chunkFits heapAligned heapFits
    accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload F state post value layout outerLocal watchedChunks
    chunksLocal chunksAligned chunksFits payloadChunks code pointerGlobal accelGlobal zeroGlobal chunkGlobal heapGlobal transactions slices
    rawLocal outLocal payloadLocal withdrawals withdrawalBound requestEntry requestBound blobEntry blobBound budget run
  exact htrPayload_tx_metadata_suffix_returned_memory_guarded pointer accelerator zeroHashes chunk array heap input inputLength count payload chunks
    withdrawalArray withdrawalCount requests requestLength raw out outerMark watched small countBound arrayHeap chunkAligned chunkFits heapAligned heapFits
    accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload state post value layout outerLocal watchedChunks
    chunksLocal chunksAligned chunksFits payloadChunks code pointerGlobal accelGlobal zeroGlobal chunkGlobal heapGlobal transactions slices
    rawLocal outLocal payloadLocal withdrawals withdrawalBound requestEntry requestBound budget run

/-- Each real fixed-size header copy preserves decoded entries, input slice
metadata and the watched word before continuing into the remaining source. -/
theorem payload_header_copy_memory_step_guarded (index next : Nat) (inputOffset outputOffset : BitVec 64)
    (outputBound : outputOffset.toNat ≤ 576) (outputAligned : outputOffset.toNat % 8 = 0)
    (source : htrPayloadAt index = .seq (.call (some (none,none)) (ofString "memcpy")
      (htrPayloadCopyArguments outputOffset inputOffset)) (htrPayloadAt next))
    (cost : BitVec 64 → BitVec 64 → Nat) (tail : PayloadHeaderSuffixMemory_guarded next cost) :
    PayloadHeaderSuffixMemory_guarded index (fun count withdrawalCount => 16 + cost count withdrawalCount) := by
  intro pointer accelerator zeroHashes chunk array heap input inputLength count payload chunks withdrawalArray withdrawalCount
    requests requestLength raw out blobs blobLength outerMark watched small countBound arrayHeap arrayChunks chunkAligned chunkFits heapAligned heapFits
    accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload F state post value layout outerLocal watchedChunks
    chunksLocal chunksAligned chunksFits payloadChunks code pointerGlobal accelGlobal zeroGlobal chunkGlobal heapGlobal transactions slices
    rawLocal outLocal payloadLocal withdrawals withdrawalBound requestEntry requestBound blobEntry blobBound budget run
  change 16 + cost count withdrawalCount ≤ state.clock at budget
  rw [source] at run
  obtain ⟨middle,normal,rest⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile _ rfl state v) run
  let arguments := htrPayloadCopyArguments outputOffset inputOffset
  have args := htrPayload_copy_arguments state chunks raw outputOffset inputOffset chunksLocal rawLocal
  have natural : (chunks + outputOffset).toNat = chunks.toNat + outputOffset.toNat :=
    BitVec.toNat_add_of_lt (by omega)
  have aligned : (chunks + outputOffset).toNat % 8 = 0 := by rw [natural,Nat.add_mod,chunksAligned,outputAligned]
  have separation := memcpy_interval_separate (chunks + outputOffset) (32#64) watched aligned
    (by rw [natural]; change _ + 32 ≤ _; omega) (Or.inl (by rw [natural]; omega))
  have frame := memcpy_call_normal_memory state middle arguments (chunks + outputOffset) (raw + inputOffset) (32#64) watched
    args code (fun offset inside => (separation offset inside).1) (fun offset inside => (separation offset inside).2)
    (by decide) (by change 16 ≤ state.clock; omega) normal
  have transfer (field p n : BitVec 64) (entry : RlpSliceEntry state payload field p n) (inside : field.toNat ≤ 4) :=
    memcpy_call_normal_decoded_frame state middle arguments (chunks + outputOffset) (raw + inputOffset) (32#64)
      payload field p n array input inputLength count.toNat args entry inside slices aligned (by rw [natural]; change _ + 32 ≤ _; omega)
      (by rw [natural]; omega) (by rw [natural]; omega) (by decide) code (by change 16 ≤ state.clock; omega) normal
  have keep (key : MlS) : middle.locals.lookup key = state.locals.lookup key := by
    have kept := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "memcpy") arguments) rfl state
      (by rw [normal]; exact Or.inl rfl)
    rw [normal] at kept
    exact kept
  have globals := memcpy_call_globals_frame arguments state code
  have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "memcpy") arguments)
  have bounded := evaluate_memcpy_call_bounded state arguments (chunks + outputOffset) (raw + inputOffset) (32#64)
    args code (by decide) (by change 16 ≤ state.clock; omega)
  unfold RunBounded at bounded
  rw [normal] at globals metadata bounded
  have spent : state.clock ≤ middle.clock + 16 := bounded.1
  have txFrame := transfer (2#64) array count transactions (by decide)
  have suffix := tail pointer accelerator zeroHashes chunk array heap input inputLength count payload chunks withdrawalArray withdrawalCount
    requests requestLength raw out blobs blobLength outerMark watched small countBound arrayHeap arrayChunks chunkAligned chunkFits heapAligned heapFits
    accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload middle post value (layout.transfer globals metadata.1)
    ((keep _).trans outerLocal) watchedChunks ((keep _).trans chunksLocal) chunksAligned chunksFits payloadChunks (metadata.1.trans code)
    (by rw [globals]; exact pointerGlobal) (by rw [globals]; exact accelGlobal) (by rw [globals]; exact zeroGlobal)
    (by rw [globals]; exact chunkGlobal) (by rw [globals]; exact heapGlobal) txFrame.1 txFrame.2
    ((keep _).trans rawLocal) ((keep _).trans outLocal) ((keep _).trans payloadLocal)
    (transfer (3#64) withdrawalArray withdrawalCount withdrawals (by decide)).1 withdrawalBound
    (transfer (4#64) requests requestLength requestEntry (by decide)).1 requestBound
    (transfer (1#64) blobs blobLength blobEntry (by decide)).1 blobBound (by omega) rest
  exact suffix.trans frame

theorem payload_header_copy_15_memory_guarded : PayloadHeaderSuffixMemory_guarded 15 (fun count wd => 16 + htrPayloadTxMetadataCost count wd) :=
  payload_header_copy_memory_step_guarded 15 16 (472#64) (384#64) (by decide) (by decide)
    source_htrPayload_copy_15 htrPayloadTxMetadataCost payload_header_tx_metadata_memory_guarded

theorem payload_header_copy_14_memory_guarded : PayloadHeaderSuffixMemory_guarded 14 (fun count wd => 16 + (16 + htrPayloadTxMetadataCost count wd)) :=
  payload_header_copy_memory_step_guarded 14 15 (440#64) (352#64) (by decide) (by decide)
    source_htrPayload_copy_14 _ payload_header_copy_15_memory_guarded

#print axioms payload_header_tx_metadata_memory_guarded
#print axioms payload_header_copy_memory_step_guarded
#print axioms payload_header_copy_15_memory_guarded
#print axioms payload_header_copy_14_memory_guarded
end InitECandidate.Runtime
