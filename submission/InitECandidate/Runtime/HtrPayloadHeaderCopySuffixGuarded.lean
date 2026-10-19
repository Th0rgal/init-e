import InitECandidate.Runtime.HtrPayloadHeaderCopySuffixBound
import InitECandidate.Runtime.HtrPayloadHeaderU64SuffixGuarded
import InitECandidate.Runtime.HtrBytesVectorDecodedFrameGuarded
import InitECandidate.Runtime.HtrPayloadHeaderU64SuffixBound
import InitECandidate.Runtime.HtrPayloadHeaderCopySource
import InitECandidate.Runtime.KeccakGlobalsFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem payload_header_copy_step_guarded (index next : Nat) (inputOffset outputOffset : BitVec 64)
    (outputBound : outputOffset.toNat ≤ 576) (outputAligned : outputOffset.toNat % 8 = 0)
    (source : htrPayloadAt index = .seq (.call (some (none,none)) (ofString "memcpy")
      (htrPayloadCopyArguments outputOffset inputOffset)) (htrPayloadAt next))
    (cost : BitVec 64 → BitVec 64 → Nat) (tail : PayloadHeaderSuffixBoundGuarded next cost) :
    PayloadHeaderSuffixBoundGuarded index (fun count withdrawalCount => 16 + cost count withdrawalCount) := by
  intro pointer accelerator zeroHashes chunk array heap input inputLength count payload chunks withdrawalArray withdrawalCount
    requests requestLength raw out blobs blobLength small countBound arrayHeap arrayChunks chunkAligned chunkFits heapAligned heapFits
    accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload F state chunksLocal chunksAligned chunksFits
    payloadChunks code pointerGlobal accelGlobal zeroGlobal chunkGlobal heapGlobal transactions slices rawLocal outLocal payloadLocal
    withdrawals withdrawalBound requestEntry requestBound blobEntry blobBound budget
  change 16 + cost count withdrawalCount ≤ state.clock at budget
  let arguments := htrPayloadCopyArguments outputOffset inputOffset
  have args := htrPayload_copy_arguments state chunks raw outputOffset inputOffset chunksLocal rawLocal
  have first : RunBounded state (.call (some (none,none)) (ofString "memcpy") arguments) 16 :=
    evaluate_memcpy_call_bounded state arguments (chunks + outputOffset) (raw + inputOffset) (32#64)
      args code (by decide) (by change 16 ≤ state.clock; omega)
  have natural : (chunks + outputOffset).toNat = chunks.toNat + outputOffset.toNat := by
    apply BitVec.toNat_add_of_lt
    omega
  have aligned : (chunks + outputOffset).toNat % 8 = 0 := by
    rw [natural,Nat.add_mod,chunksAligned,outputAligned]
  rw [source]
  exact RunBounded.seq first budget (by
    intro post normal postCode remaining
    change evaluateHOLFiniteState state (.call (some (none,none)) (ofString "memcpy") arguments) = (none,post) at normal
    have transfer (field p n : BitVec 64) (entry : RlpSliceEntry state payload field p n) (inside : field.toNat ≤ 4) :=
      memcpy_call_normal_decoded_frame state post arguments (chunks + outputOffset) (raw + inputOffset) (32#64)
        payload field p n array input inputLength count.toNat args entry inside slices aligned (by rw [natural]; change _ + 32 ≤ _; omega)
        (by rw [natural]; omega) (by rw [natural]; omega) (by decide) code (by change 16 ≤ state.clock; omega) normal
    have keep (key : MlS) : post.locals.lookup key = state.locals.lookup key := by
      have kept := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "memcpy") arguments) rfl state
        (by rw [normal]; exact Or.inl rfl)
      simpa only [normal] using kept
    have globals := memcpy_call_globals_frame arguments state code
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

theorem payload_header_copy_8_bound_guarded : PayloadHeaderSuffixBoundGuarded 8 htrPayloadHeaderCost8 :=
  payload_header_copy_step_guarded 8 9 (372#64) (160#64) (by decide) (by decide)
    source_htrPayload_copy_8 htrPayloadHeaderCost9 payload_header_u64_9_bound_guarded

#print axioms payload_header_copy_step_guarded
#print axioms payload_header_copy_8_bound_guarded
end InitECandidate.Runtime
