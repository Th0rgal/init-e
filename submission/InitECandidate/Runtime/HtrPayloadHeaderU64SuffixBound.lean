import InitECandidate.Runtime.HtrPayloadBytesListSuffixBound
import InitECandidate.Runtime.HtrPayloadHeaderU64Source
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option linter.unusedVariables false in
/-- A header suffix with all concrete decoded metadata, slice and layout premises. -/
def PayloadHeaderSuffixBound (index : Nat) (cost : BitVec 64 → BitVec 64 → Nat) : Prop :=
  ∀ (pointer accelerator zeroHashes chunk array heap input inputLength count payload chunks withdrawalArray withdrawalCount requests requestLength raw out blobs blobLength : BitVec 64)
    (small : inputLength.toNat ≤ 134217712) (countBound : count.toNat ≤ 134217712)
    (arrayHeap : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (arrayChunks : array.toNat + count.toNat * 16 ≤ chunks.toNat)
    (chunkAligned : chunk.toNat % 8 = 0) (chunkFits : chunk.toNat + 32 ≤ array.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ array.toNat) (pointerFits : pointer.toNat + 64 ≤ array.toNat)
    (payloadHeap : payload.toNat + 72 < heap.toNat)
    (chunkPayload : chunk.toNat + 32 ≤ payload.toNat)
    (accelPayload : accelerator.toNat + 96 ≤ payload.toNat) (pointerPayload : pointer.toNat + 64 ≤ payload.toNat)
    {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (budget : cost count withdrawalCount ≤ state.clock),
    RunBounded state (htrPayloadAt index) (cost count withdrawalCount)

def htrPayloadHeaderCost13 (count withdrawalCount : BitVec 64) : Nat :=
  (htrBytesListBodyCost + 1) + (16 + (16 + htrPayloadTxMetadataCost count withdrawalCount))

theorem payload_header_bytes_list_bound : PayloadHeaderSuffixBound 13 htrPayloadHeaderCost13 :=
  runBounded_htrPayload_bytes_list_suffix

theorem payload_header_u64_step (index next : Nat) (inputOffset outputOffset : BitVec 64)
    (outputBound : outputOffset.toNat ≤ 576) (outputAligned : outputOffset.toNat % 8 = 0)
    (source : htrPayloadAt index = .seq (.call (some (none,none)) (ofString "htr_u64_at")
      (htrPayloadU64Arguments inputOffset outputOffset)) (htrPayloadAt next))
    (cost : BitVec 64 → BitVec 64 → Nat) (tail : PayloadHeaderSuffixBound next cost) :
    PayloadHeaderSuffixBound index (fun count withdrawalCount => 30 + cost count withdrawalCount) := by
  intro pointer accelerator zeroHashes chunk array heap input inputLength count payload chunks withdrawalArray withdrawalCount
    requests requestLength raw out blobs blobLength small countBound arrayHeap arrayChunks chunkAligned chunkFits heapAligned heapFits
    accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload F state chunksLocal chunksAligned chunksFits
    payloadChunks code pointerGlobal accelGlobal zeroGlobal chunkGlobal heapGlobal transactions slices rawLocal outLocal payloadLocal
    withdrawals withdrawalBound requestEntry requestBound blobEntry blobBound budget
  change 30 + cost count withdrawalCount ≤ state.clock at budget
  let arguments := htrPayloadU64Arguments inputOffset outputOffset
  have args := htrPayload_u64_arguments state raw chunks inputOffset outputOffset rawLocal chunksLocal
  have first : RunBounded state (.call (some (none,none)) (ofString "htr_u64_at") arguments) 30 :=
    RunBounded.ofProg (ProgBounded.call htrU64At_funBounded none arguments) code (by omega)
  have natural : (chunks + outputOffset).toNat = chunks.toNat + outputOffset.toNat := by
    apply BitVec.toNat_add_of_lt
    omega
  have aligned : (chunks + outputOffset).toNat % 8 = 0 := by
    rw [natural,Nat.add_mod,chunksAligned,outputAligned]
  rw [source]
  exact RunBounded.seq first budget (by
    intro post normal postCode remaining
    change evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_u64_at") arguments) = (none,post) at normal
    have transfer (field p n : BitVec 64) (entry : RlpSliceEntry state payload field p n) (inside : field.toNat ≤ 4) :=
      htrU64At_call_normal_decoded_frame state post arguments (chunks + outputOffset) (raw + inputOffset)
        payload field p n array input inputLength count.toNat args entry inside slices aligned (by rw [natural]; omega)
        (by rw [natural]; omega) (by rw [natural]; omega) code (by omega) normal
    have keep (key : MlS) : post.locals.lookup key = state.locals.lookup key := by
      have kept := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "htr_u64_at") arguments) rfl state
        (by rw [normal]; exact Or.inl rfl)
      simpa only [normal] using kept
    have globals := htrU64At_call_globals arguments state code
    rw [normal] at globals
    have txFrame := transfer (2#64) array count transactions (by decide)
    exact tail pointer accelerator zeroHashes chunk array heap input inputLength count payload chunks withdrawalArray withdrawalCount
      requests requestLength raw out blobs blobLength small countBound arrayHeap arrayChunks chunkAligned chunkFits heapAligned heapFits
      accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload post
      ((keep _).trans chunksLocal) chunksAligned chunksFits payloadChunks (postCode.trans code)
      (by rw [globals]; exact pointerGlobal) (by rw [globals]; exact accelGlobal) (by rw [globals]; exact zeroGlobal)
      (by rw [globals]; exact chunkGlobal) (by rw [globals]; exact heapGlobal) txFrame.1 txFrame.2
      ((keep _).trans rawLocal) ((keep _).trans outLocal) ((keep _).trans payloadLocal)
      (transfer (3#64) withdrawalArray withdrawalCount withdrawals (by decide)).1 withdrawalBound
      (transfer (4#64) requests requestLength requestEntry (by decide)).1 requestBound
      (transfer (1#64) blobs blobLength blobEntry (by decide)).1 blobBound remaining)

def htrPayloadHeaderCost12 (count withdrawalCount : BitVec 64) : Nat :=
  30 + htrPayloadHeaderCost13 count withdrawalCount

theorem payload_header_u64_12_bound : PayloadHeaderSuffixBound 12 htrPayloadHeaderCost12 :=
  payload_header_u64_step 12 13 (428#64) (288#64) (by decide) (by decide)
    source_htrPayload_u64_12 htrPayloadHeaderCost13 payload_header_bytes_list_bound

def htrPayloadHeaderCost11 (count withdrawalCount : BitVec 64) : Nat :=
  30 + htrPayloadHeaderCost12 count withdrawalCount

theorem payload_header_u64_11_bound : PayloadHeaderSuffixBound 11 htrPayloadHeaderCost11 :=
  payload_header_u64_step 11 12 (420#64) (256#64) (by decide) (by decide)
    source_htrPayload_u64_11 htrPayloadHeaderCost12 payload_header_u64_12_bound

def htrPayloadHeaderCost10 (count withdrawalCount : BitVec 64) : Nat :=
  30 + htrPayloadHeaderCost11 count withdrawalCount

theorem payload_header_u64_10_bound : PayloadHeaderSuffixBound 10 htrPayloadHeaderCost10 :=
  payload_header_u64_step 10 11 (412#64) (224#64) (by decide) (by decide)
    source_htrPayload_u64_10 htrPayloadHeaderCost11 payload_header_u64_11_bound

def htrPayloadHeaderCost9 (count withdrawalCount : BitVec 64) : Nat :=
  30 + htrPayloadHeaderCost10 count withdrawalCount

theorem payload_header_u64_9_bound : PayloadHeaderSuffixBound 9 htrPayloadHeaderCost9 :=
  payload_header_u64_step 9 10 (404#64) (192#64) (by decide) (by decide)
    source_htrPayload_u64_9 htrPayloadHeaderCost10 payload_header_u64_10_bound

#print axioms payload_header_bytes_list_bound
#print axioms payload_header_u64_step
#print axioms payload_header_u64_12_bound
#print axioms payload_header_u64_11_bound
#print axioms payload_header_u64_10_bound
#print axioms payload_header_u64_9_bound
end InitECandidate.Runtime
