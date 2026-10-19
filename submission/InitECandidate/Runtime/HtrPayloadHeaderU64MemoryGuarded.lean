import InitECandidate.Runtime.HtrPayloadHeaderU64Memory
import InitECandidate.Runtime.HtrPayloadBytesListSuffixMemoryGuarded
import InitECandidate.Runtime.HtrBytesVectorDecodedFrameGuarded
import InitECandidate.Runtime.HtrPayloadBytesListSuffixMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- The actual header scalar hashes preserve watched memory and decoded
entries before continuing into the remaining original payload body. -/
theorem payload_header_u64_memory_step_guarded (index next : Nat) (inputOffset outputOffset : BitVec 64)
    (outputBound : outputOffset.toNat ≤ 576) (outputAligned : outputOffset.toNat % 8 = 0)
    (source : htrPayloadAt index = .seq (.call (some (none,none)) (ofString "htr_u64_at")
      (htrPayloadU64Arguments inputOffset outputOffset)) (htrPayloadAt next))
    (cost : BitVec 64 → BitVec 64 → Nat) (tail : PayloadHeaderSuffixMemory_guarded next cost) :
    PayloadHeaderSuffixMemory_guarded index (fun count withdrawalCount => 30 + cost count withdrawalCount) := by
  intro pointer accelerator zeroHashes chunk array heap input inputLength count payload chunks withdrawalArray withdrawalCount
    requests requestLength raw out blobs blobLength outerMark watched small countBound arrayHeap arrayChunks chunkAligned chunkFits heapAligned heapFits
    accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload F state post value layout outerLocal watchedChunks
    chunksLocal chunksAligned chunksFits payloadChunks code pointerGlobal accelGlobal zeroGlobal chunkGlobal heapGlobal transactions slices
    rawLocal outLocal payloadLocal withdrawals withdrawalBound requestEntry requestBound blobEntry blobBound budget run
  change 30 + cost count withdrawalCount ≤ state.clock at budget
  rw [source] at run
  obtain ⟨middle,normal,rest⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile _ rfl state v) run
  let arguments := htrPayloadU64Arguments inputOffset outputOffset
  have args := htrPayload_u64_arguments state raw chunks inputOffset outputOffset rawLocal chunksLocal
  have natural : (chunks + outputOffset).toNat = chunks.toNat + outputOffset.toNat :=
    BitVec.toNat_add_of_lt (by omega)
  have aligned : (chunks + outputOffset).toNat % 8 = 0 := by rw [natural,Nat.add_mod,chunksAligned,outputAligned]
  have frame := htrU64At_call_normal_memory state middle arguments (raw + inputOffset) (chunks + outputOffset) watched
    args code aligned (by rw [natural]; omega) (Or.inl (by rw [natural]; omega)) (by omega) normal
  have transfer (field p n : BitVec 64) (entry : RlpSliceEntry state payload field p n) (inside : field.toNat ≤ 4) :=
    htrU64At_call_normal_decoded_frame state middle arguments (chunks + outputOffset) (raw + inputOffset)
      payload field p n array input inputLength count.toNat args entry inside slices aligned (by rw [natural]; omega)
      (by rw [natural]; omega) (by rw [natural]; omega) code (by omega) normal
  have keep (key : MlS) : middle.locals.lookup key = state.locals.lookup key := by
    have kept := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "htr_u64_at") arguments) rfl state
      (by rw [normal]; exact Or.inl rfl)
    rw [normal] at kept
    exact kept
  have globals := htrU64At_call_globals arguments state code
  have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "htr_u64_at") arguments)
  have bounded := RunBounded.ofProg (ProgBounded.call htrU64At_funBounded (destination := none) arguments) code (by omega)
  unfold RunBounded at bounded
  rw [normal] at globals metadata bounded
  have spent : state.clock ≤ middle.clock + 30 := bounded.1
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

theorem payload_header_u64_12_memory_guarded : PayloadHeaderSuffixMemory_guarded 12 htrPayloadHeaderCost12 :=
  payload_header_u64_memory_step_guarded 12 13 (428#64) (288#64) (by decide) (by decide)
    source_htrPayload_u64_12 htrPayloadHeaderCost13 payload_header_bytes_list_memory_guarded

theorem payload_header_u64_11_memory_guarded : PayloadHeaderSuffixMemory_guarded 11 htrPayloadHeaderCost11 :=
  payload_header_u64_memory_step_guarded 11 12 (420#64) (256#64) (by decide) (by decide)
    source_htrPayload_u64_11 htrPayloadHeaderCost12 payload_header_u64_12_memory_guarded

theorem payload_header_u64_10_memory_guarded : PayloadHeaderSuffixMemory_guarded 10 htrPayloadHeaderCost10 :=
  payload_header_u64_memory_step_guarded 10 11 (412#64) (224#64) (by decide) (by decide)
    source_htrPayload_u64_10 htrPayloadHeaderCost11 payload_header_u64_11_memory_guarded

theorem payload_header_u64_9_memory_guarded : PayloadHeaderSuffixMemory_guarded 9 htrPayloadHeaderCost9 :=
  payload_header_u64_memory_step_guarded 9 10 (404#64) (192#64) (by decide) (by decide)
    source_htrPayload_u64_9 htrPayloadHeaderCost10 payload_header_u64_10_memory_guarded

#print axioms payload_header_u64_memory_step_guarded
#print axioms payload_header_u64_12_memory_guarded
#print axioms payload_header_u64_11_memory_guarded
#print axioms payload_header_u64_10_memory_guarded
#print axioms payload_header_u64_9_memory_guarded
end InitECandidate.Runtime
