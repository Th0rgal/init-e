import InitECandidate.Runtime.HtrPayloadHeaderVectorSuffixBound
import InitECandidate.Runtime.HtrPayloadHeaderCopySuffixGuarded
import InitECandidate.Runtime.HtrBytesVectorDecodedFrameGuarded
import InitECandidate.Runtime.HtrPayloadHeaderCopySuffixBound
import InitECandidate.Runtime.HtrPayloadHeaderVectorSource
import InitECandidate.Runtime.HtrBytesVectorDecodedFrame
import InitECandidate.Runtime.HtrBytesVectorGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem payload_header_vector_step_guarded (index next : Nat) (inputOffset length outputOffset : BitVec 64)
    (smallLength : length.toNat ≤ 134217712)
    (outputBound : outputOffset.toNat ≤ 576) (outputAligned : outputOffset.toNat % 8 = 0)
    (source : htrPayloadAt index = .seq (.call (some (none,none)) (ofString "htr_bytes_vector")
      (htrPayloadVectorArguments inputOffset length outputOffset)) (htrPayloadAt next))
    (cost : BitVec 64 → BitVec 64 → Nat) (tail : PayloadHeaderSuffixBoundGuarded next cost) :
    PayloadHeaderSuffixBoundGuarded index (fun count withdrawalCount => (htrBytesVectorBodyCost + 1) + cost count withdrawalCount) := by
  intro pointer accelerator zeroHashes chunk array heap input inputLength count payload chunks withdrawalArray withdrawalCount
    requests requestLength raw out blobs blobLength small countBound arrayHeap arrayChunks chunkAligned chunkFits heapAligned heapFits
    accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload F state chunksLocal chunksAligned chunksFits
    payloadChunks code pointerGlobal accelGlobal zeroGlobal chunkGlobal heapGlobal transactions slices rawLocal outLocal payloadLocal
    withdrawals withdrawalBound requestEntry requestBound blobEntry blobBound budget
  change (htrBytesVectorBodyCost + 1) + cost count withdrawalCount ≤ state.clock at budget
  let arguments := htrPayloadVectorArguments inputOffset length outputOffset
  have args := htrPayload_vector_arguments state raw chunks inputOffset length outputOffset rawLocal chunksLocal
  have first : RunBounded state (.call (some (none,none)) (ofString "htr_bytes_vector") arguments) (htrBytesVectorBodyCost + 1) :=
    runBounded_htrBytesVector_call state none arguments (raw + inputOffset) length (chunks + outputOffset) heap
      args smallLength heapGlobal heapFits code (by omega)
  have natural : (chunks + outputOffset).toNat = chunks.toNat + outputOffset.toNat := by
    apply BitVec.toNat_add_of_lt
    omega
  have aligned : (chunks + outputOffset).toNat % 8 = 0 := by
    rw [natural,Nat.add_mod,chunksAligned,outputAligned]
  rw [source]
  exact RunBounded.seq first budget (by
    intro post normal postCode remaining
    change evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_bytes_vector") arguments) = (none,post) at normal
    have transfer (field p n : BitVec 64) (entry : RlpSliceEntry state payload field p n) (inside : field.toNat ≤ 4) :=
      htrBytesVector_call_normal_decoded_frame_guarded state post arguments pointer accelerator zeroHashes
        (raw + inputOffset) length heap (chunks + outputOffset) payload field p n array input inputLength count.toNat
        args pointerGlobal accelGlobal zeroGlobal heapGlobal entry inside slices aligned (by rw [natural]; omega)
        (by rw [natural]; omega) (by rw [natural]; omega) smallLength heapAligned heapFits payloadHeap arrayHeap
        accelAligned accelPayload pointerPayload (fun nz => accelFits (by intro z; subst count; exact nz rfl)) (fun nz => pointerFits (by intro z; subst count; exact nz rfl)) code (by omega) normal
    have keep (key : MlS) : post.locals.lookup key = state.locals.lookup key := by
      have kept := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "htr_bytes_vector") arguments) rfl state
        (by rw [normal]; exact Or.inl rfl)
      simpa only [normal] using kept
    have globals := htrBytesVector_call_normal_globals state post arguments (raw + inputOffset) length (chunks + outputOffset) heap args heapGlobal code normal
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

theorem payload_header_vector_7_bound_guarded : PayloadHeaderSuffixBoundGuarded 7 htrPayloadHeaderCost7 :=
  payload_header_vector_step_guarded 7 8 (116#64) (256#64) (128#64) (by decide) (by decide) (by decide)
    source_htrPayload_vector_7 htrPayloadHeaderCost8 payload_header_copy_8_bound_guarded

theorem payload_header_copy_6_bound_guarded : PayloadHeaderSuffixBoundGuarded 6 htrPayloadHeaderCost6 :=
  payload_header_copy_step_guarded 6 7 (84#64) (96#64) (by decide) (by decide)
    source_htrPayload_copy_6 htrPayloadHeaderCost7 payload_header_vector_7_bound_guarded

theorem payload_header_copy_5_bound_guarded : PayloadHeaderSuffixBoundGuarded 5 htrPayloadHeaderCost5 :=
  payload_header_copy_step_guarded 5 6 (52#64) (64#64) (by decide) (by decide)
    source_htrPayload_copy_5 htrPayloadHeaderCost6 payload_header_copy_6_bound_guarded

theorem payload_header_vector_4_bound_guarded : PayloadHeaderSuffixBoundGuarded 4 htrPayloadHeaderCost4 :=
  payload_header_vector_step_guarded 4 5 (32#64) (20#64) (32#64) (by decide) (by decide) (by decide)
    source_htrPayload_vector_4 htrPayloadHeaderCost5 payload_header_copy_5_bound_guarded

#print axioms payload_header_vector_step_guarded
#print axioms payload_header_vector_7_bound_guarded
#print axioms payload_header_copy_6_bound_guarded
#print axioms payload_header_copy_5_bound_guarded
#print axioms payload_header_vector_4_bound_guarded
end InitECandidate.Runtime
