import InitECandidate.Runtime.HtrPayloadHeaderVectorMemory
import InitECandidate.Runtime.HtrPayloadHeaderU64MemoryGuarded
import InitECandidate.Runtime.HtrBytesVectorDecodedFrameGuarded
import InitECandidate.Runtime.HtrPayloadHeaderU64Memory
import InitECandidate.Runtime.HtrPayloadHeaderVectorSuffixBound
import InitECandidate.Runtime.HtrBytesVectorMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- Fixed-size vector hashes retain watched memory, input-slice metadata and
all decoded entries before the remaining original header/body execution. -/
theorem payload_header_vector_memory_step_guarded (index next : Nat) (inputOffset length outputOffset : BitVec 64)
    (smallLength : length.toNat ≤ 134217712)
    (outputBound : outputOffset.toNat ≤ 576) (outputAligned : outputOffset.toNat % 8 = 0)
    (source : htrPayloadAt index = .seq (.call (some (none,none)) (ofString "htr_bytes_vector")
      (htrPayloadVectorArguments inputOffset length outputOffset)) (htrPayloadAt next))
    (cost : BitVec 64 → BitVec 64 → Nat) (tail : PayloadHeaderSuffixMemory_guarded next cost) :
    PayloadHeaderSuffixMemory_guarded index (fun count withdrawalCount => (htrBytesVectorBodyCost + 1) + cost count withdrawalCount) := by
  intro pointer accelerator zeroHashes chunk array heap input inputLength count payload chunks withdrawalArray withdrawalCount
    requests requestLength raw out blobs blobLength outerMark watched small countBound arrayHeap arrayChunks chunkAligned chunkFits heapAligned heapFits
    accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload F state post value layout outerLocal watchedChunks
    chunksLocal chunksAligned chunksFits payloadChunks code pointerGlobal accelGlobal zeroGlobal chunkGlobal heapGlobal transactions slices
    rawLocal outLocal payloadLocal withdrawals withdrawalBound requestEntry requestBound blobEntry blobBound budget run
  change (htrBytesVectorBodyCost + 1) + cost count withdrawalCount ≤ state.clock at budget
  rw [source] at run
  obtain ⟨middle,normal,rest⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile _ rfl state v) run
  let arguments := htrPayloadVectorArguments inputOffset length outputOffset
  have args := htrPayload_vector_arguments state raw chunks inputOffset length outputOffset rawLocal chunksLocal
  have natural : (chunks + outputOffset).toNat = chunks.toNat + outputOffset.toNat :=
    BitVec.toNat_add_of_lt (by omega)
  have aligned : (chunks + outputOffset).toNat % 8 = 0 := by rw [natural,Nat.add_mod,chunksAligned,outputAligned]
  have enough : htrBytesVectorBodyCost + 1 ≤ state.clock :=
    (Nat.le_add_right (htrBytesVectorBodyCost + 1) (cost count withdrawalCount)).trans budget
  have frame := htrBytesVector_call_normal_memory state middle arguments pointer accelerator zeroHashes (raw + inputOffset) length heap
    (chunks + outputOffset) watched args pointerGlobal accelGlobal zeroGlobal heapGlobal aligned (by rw [natural]; omega)
    (Or.inl (by rw [natural]; omega)) smallLength heapAligned heapFits layout.heapBefore accelAligned layout.accelFits layout.shaFits
    layout.accelOutside layout.shaOutside code enough normal
  have transfer (field p n : BitVec 64) (entry : RlpSliceEntry state payload field p n) (inside : field.toNat ≤ 4) :=
    htrBytesVector_call_normal_decoded_frame_guarded state middle arguments pointer accelerator zeroHashes
      (raw + inputOffset) length heap (chunks + outputOffset) payload field p n array input inputLength count.toNat
      args pointerGlobal accelGlobal zeroGlobal heapGlobal entry inside slices aligned (by rw [natural]; omega)
      (by rw [natural]; omega) (by rw [natural]; omega) smallLength heapAligned heapFits payloadHeap arrayHeap
      accelAligned accelPayload pointerPayload (fun nz => accelFits (by intro z; subst count; exact nz rfl)) (fun nz => pointerFits (by intro z; subst count; exact nz rfl)) code enough normal
  have keep (key : MlS) : middle.locals.lookup key = state.locals.lookup key := by
    have kept := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "htr_bytes_vector") arguments) rfl state
      (by rw [normal]; exact Or.inl rfl)
    rw [normal] at kept
    exact kept
  have globals := htrBytesVector_call_normal_globals state middle arguments (raw + inputOffset) length (chunks + outputOffset) heap args heapGlobal code normal
  have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "htr_bytes_vector") arguments)
  have bounded := runBounded_htrBytesVector_call state none arguments (raw + inputOffset) length (chunks + outputOffset) heap
    args smallLength heapGlobal heapFits code enough
  unfold RunBounded at bounded
  rw [normal] at metadata bounded
  have spent : state.clock ≤ middle.clock + (htrBytesVectorBodyCost + 1) := bounded.1
  have remaining : cost count withdrawalCount ≤ middle.clock := by
    generalize htrBytesVectorBodyCost = vc at budget spent
    omega
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
    (transfer (1#64) blobs blobLength blobEntry (by decide)).1 blobBound remaining rest
  exact suffix.trans frame

theorem payload_header_copy_8_memory_guarded : PayloadHeaderSuffixMemory_guarded 8 htrPayloadHeaderCost8 :=
  payload_header_copy_memory_step_guarded 8 9 (372#64) (160#64) (by decide) (by decide)
    source_htrPayload_copy_8 htrPayloadHeaderCost9 payload_header_u64_9_memory_guarded

theorem payload_header_vector_7_memory_guarded : PayloadHeaderSuffixMemory_guarded 7 htrPayloadHeaderCost7 :=
  payload_header_vector_memory_step_guarded 7 8 (116#64) (256#64) (128#64) (by decide) (by decide) (by decide)
    source_htrPayload_vector_7 htrPayloadHeaderCost8 payload_header_copy_8_memory_guarded

theorem payload_header_copy_6_memory_guarded : PayloadHeaderSuffixMemory_guarded 6 htrPayloadHeaderCost6 :=
  payload_header_copy_memory_step_guarded 6 7 (84#64) (96#64) (by decide) (by decide)
    source_htrPayload_copy_6 htrPayloadHeaderCost7 payload_header_vector_7_memory_guarded

theorem payload_header_copy_5_memory_guarded : PayloadHeaderSuffixMemory_guarded 5 htrPayloadHeaderCost5 :=
  payload_header_copy_memory_step_guarded 5 6 (52#64) (64#64) (by decide) (by decide)
    source_htrPayload_copy_5 htrPayloadHeaderCost6 payload_header_copy_6_memory_guarded

theorem payload_header_vector_4_memory_guarded : PayloadHeaderSuffixMemory_guarded 4 htrPayloadHeaderCost4 :=
  payload_header_vector_memory_step_guarded 4 5 (32#64) (20#64) (32#64) (by decide) (by decide) (by decide)
    source_htrPayload_vector_4 htrPayloadHeaderCost5 payload_header_copy_5_memory_guarded

#print axioms payload_header_vector_memory_step_guarded
#print axioms payload_header_copy_8_memory_guarded
#print axioms payload_header_vector_7_memory_guarded
#print axioms payload_header_copy_6_memory_guarded
#print axioms payload_header_copy_5_memory_guarded
#print axioms payload_header_vector_4_memory_guarded
end InitECandidate.Runtime
