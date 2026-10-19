import InitECandidate.Runtime.HtrPayloadHeaderCopySource
import InitECandidate.Runtime.HtrPayloadTxMetadataSuffixBound
import InitECandidate.Runtime.KeccakGlobalsFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def htrPayloadTxMetadataCost (count withdrawalCount : BitVec 64) : Nat :=
  1 + (2 + ((count.toNat * (htrPbytesBodyCost + 2) + (htrPlistChunksCost + 2)) + htrPayloadWithdrawalTotalCost withdrawalCount))

theorem runBounded_htrPayload_header_copy15_suffix (pointer accelerator zeroHashes chunk array heap input inputLength count payload chunks withdrawalArray withdrawalCount requests requestLength raw out : BitVec 64)
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
    (budget : 16 + htrPayloadTxMetadataCost count withdrawalCount ≤ state.clock) :
    RunBounded state (htrPayloadAt 15) (16 + htrPayloadTxMetadataCost count withdrawalCount) := by
  let arguments := htrPayloadCopyArguments (384#64) (472#64)
  have args := htrPayload_copy_arguments state chunks raw (384#64) (472#64) chunksLocal rawLocal
  have first : RunBounded state (.call (some (none,none)) (ofString "memcpy") arguments) 16 :=
    evaluate_memcpy_call_bounded state arguments (chunks + (384#64)) (raw + (472#64)) (32#64)
      args code (by decide) (by change 16 ≤ state.clock; omega)
  have natural : (chunks + (384#64)).toNat = chunks.toNat + 384 := by
    apply BitVec.toNat_add_of_lt
    change chunks.toNat + 384 < 2 ^ 64
    omega
  have aligned : (chunks + (384#64)).toNat % 8 = 0 := by
    rw [natural,Nat.add_mod,chunksAligned]
  rw [source_htrPayload_copy_15]
  exact RunBounded.seq first budget (by
    intro next normal nextCode remaining
    change evaluateHOLFiniteState state (.call (some (none,none)) (ofString "memcpy") arguments) = (none,next) at normal
    have transfer (index p n : BitVec 64) (entry : RlpSliceEntry state payload index p n) (inside : index.toNat ≤ 4) :=
      memcpy_call_normal_decoded_frame state next arguments (chunks + (384#64)) (raw + (472#64)) (32#64)
        payload index p n array input inputLength count.toNat args entry inside slices aligned (by rw [natural]; change _ + 32 ≤ _; omega)
        (by rw [natural]; omega) (by rw [natural]; omega) (by decide) code (by change 16 ≤ state.clock; omega) normal
    have keep (key : MlS) : next.locals.lookup key = state.locals.lookup key := by
      have kept := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "memcpy") arguments) rfl state
        (by rw [normal]; exact Or.inl rfl)
      simpa only [normal] using kept
    have globals := memcpy_call_globals_frame arguments state code
    rw [normal] at globals
    have txFrame := transfer (2#64) array count transactions (by decide)
    exact runBounded_htrPayload_tx_metadata_suffix pointer accelerator zeroHashes chunk array heap input inputLength count payload chunks
      withdrawalArray withdrawalCount requests requestLength raw out small countBound arrayHeap chunkAligned chunkFits heapAligned heapFits
      accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload next
      ((keep _).trans chunksLocal) chunksAligned chunksFits payloadChunks (nextCode.trans code)
      (by rw [globals]; exact pointerGlobal) (by rw [globals]; exact accelGlobal) (by rw [globals]; exact zeroGlobal)
      (by rw [globals]; exact chunkGlobal) (by rw [globals]; exact heapGlobal) txFrame.1 txFrame.2
      ((keep _).trans rawLocal) ((keep _).trans outLocal) ((keep _).trans payloadLocal)
      (transfer (3#64) withdrawalArray withdrawalCount withdrawals (by decide)).1 withdrawalBound
      (transfer (4#64) requests requestLength requestEntry (by decide)).1 requestBound remaining)

#print axioms runBounded_htrPayload_header_copy15_suffix
end InitECandidate.Runtime
