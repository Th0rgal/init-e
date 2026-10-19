import InitECandidate.Runtime.HtrPayloadWithdrawalBlockMemory
import InitECandidate.Runtime.RlpSliceInputPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The entire withdrawal block retains the concrete request pointer/length
metadata required by the final payload hashing suffix. -/
theorem htrPayload_withdrawal_block_preserves_requests {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator zeroHashes chunk array roots heap count chunks mark payload requests length : BitVec 64) (rank : Nat)
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
    (budget : rank * (htrWithdrawalBodyCost + 2) + (htrPlistChunksCost + 2) ≤ state.clock)
    (run : evaluateHOLFiniteState state htrPayloadWithdrawalBlock = (none,post)) :
    RlpSliceEntry post payload (4#64) requests length := by
  have frame (watched : BitVec 64) (lo : payload.toNat ≤ watched.toNat)
      (hi : watched.toNat ≤ payload.toNat + 72) : post.memory watched = state.memory watched := by
    exact htrPayload_withdrawal_block_normal_memory state post pointer accelerator zeroHashes chunk array roots count chunks heap mark watched rank
      valid rootsAligned rootsFits (by omega) chunksLocal markLocal pointerGlobal accelGlobal chunkGlobal zeroGlobal valid.heapGlobal
      chunksAligned chunksFits (by omega) countBound chunkAligned (by omega) (Or.inr (by omega)) heapAligned heapFits (by omega)
      accelAligned (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)) code budget run
  have first : (payload + (64#64)).toNat = payload.toNat + 64 := by
    apply BitVec.toNat_add_of_lt
    change payload.toNat + 64 < 2 ^ 64
    omega
  have last : (payload + (72#64)).toNat = payload.toNat + 72 := by
    apply BitVec.toNat_add_of_lt
    change payload.toNat + 72 < 2 ^ 64
    omega
  have pointerFrame := frame (payload + (64#64)) (by rw [first]; omega) (by rw [first]; omega)
  have lengthFrame := frame (payload + (72#64)) (by rw [last]; omega) (by rw [last])
  have metadata := evaluateHOLFiniteState_metadata state htrPayloadWithdrawalBlock
  rw [run] at metadata
  exact entry.after_frame state post payload (4#64) requests length metadata.2.1 pointerFrame
    (by simpa only [BitVec.add_assoc,show (4#64) * (16#64) + (8#64) = (72#64) by decide] using lengthFrame)

#print axioms htrPayload_withdrawal_block_preserves_requests
end InitECandidate.Runtime
