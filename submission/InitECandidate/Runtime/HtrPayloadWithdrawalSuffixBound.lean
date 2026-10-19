import InitECandidate.Runtime.HtrPayloadWithdrawalBlockRequestsFrame
import InitECandidate.Runtime.HtrPayloadPostWithdrawalBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem runBounded_htrPayload_withdrawal_suffix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer accelerator zeroHashes chunk array roots heap count chunks mark payload requests length raw out : BitVec 64) (rank : Nat)
    (rawLocal : state.locals.lookup (ofString "raw") = some (.val (.word raw)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (payloadLocal : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (lengthBound : length.toNat ≤ 134217712) (markBound : mark.toNat ≤ 33806089496)
    (chunksLocal : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (markLocal : state.locals.lookup (ofString "m2") = some (.val (.word mark)))
    (chunksAligned : chunks.toNat % 8 = 0) (chunksFits : chunks.toNat + 608 ≤ 33806089496)
    (payloadChunks : payload.toNat + 72 < chunks.toNat)
    (chunkAligned : chunk.toNat % 8 = 0) (chunkPayload : chunk.toNat + 32 ≤ payload.toNat)
    (chunkGlobal : state.globals.lookup (ofString "ssz_len_chunk") = some (.val (.word chunk)))
    (countBound : count.toNat ≤ 134217712)
    (rootsAligned : roots.toNat % 8 = 0) (rootsFits : roots.toNat + count.toNat * 32 ≤ 33806089496)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496)
    (payloadRoots : payload.toNat + 72 < roots.toNat) (payloadHeap : payload.toNat + 72 < heap.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelPayload : accelerator.toNat + 96 ≤ payload.toNat) (pointerPayload : pointer.toNat + 64 ≤ payload.toNat)
    (code : state.code = originalRuntimeCode)
    (valid : HtrPayloadWithdrawalState array roots heap count state rank)
    (pointerGlobal : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (accelGlobal : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (zeroGlobal : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (entry : RlpSliceEntry state payload (4#64) requests length)
    (budget : (rank * (htrWithdrawalBodyCost + 2) + (htrPlistChunksCost + 2)) + htrPayloadPostWithdrawalCost ≤ state.clock) :
    RunBounded state (htrPayloadAt 28)
      ((rank * (htrWithdrawalBodyCost + 2) + (htrPlistChunksCost + 2)) + htrPayloadPostWithdrawalCost) := by
  unfold RunBounded
  rw [evaluate_htrPayload_withdrawal_block_source]
  change RunBounded state (.seq htrPayloadWithdrawalBlock (htrPayloadAt 31)) _
  have first := runBounded_htrPayload_withdrawal_block array roots heap count countBound heapFits state rank chunks
    code valid chunksLocal (by omega)
  exact RunBounded.seq first budget (by
    intro next normal nextCode remaining
    have entryKept := htrPayload_withdrawal_block_preserves_requests state next pointer accelerator zeroHashes chunk
      array roots heap count chunks mark payload requests length rank chunksLocal markLocal chunksAligned chunksFits payloadChunks
      chunkAligned chunkPayload chunkGlobal countBound rootsAligned rootsFits heapAligned heapFits payloadRoots payloadHeap
      accelAligned accelPayload pointerPayload code valid pointerGlobal accelGlobal zeroGlobal entry (by omega) normal
    have keep (key : MlS) (different : key ≠ ofString "i") : next.locals.lookup key = state.locals.lookup key :=
      htrPayload_withdrawal_block_local_frame state next key different normal
    have heapKept := htrPayload_withdrawal_block_normal_heap state next mark markLocal code normal
    exact payload_post_withdrawal_suffix next payload raw chunks out requests length mark
      ⟨(keep _ (by decide)).trans payloadLocal,(keep _ (by decide)).trans rawLocal,
        (keep _ (by decide)).trans chunksLocal,(keep _ (by decide)).trans outLocal⟩
      entryKept lengthBound chunksAligned chunksFits payloadChunks heapKept markBound (nextCode.trans code) remaining)

#print axioms runBounded_htrPayload_withdrawal_suffix
end InitECandidate.Runtime
