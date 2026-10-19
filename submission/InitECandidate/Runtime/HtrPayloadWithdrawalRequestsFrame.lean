import InitECandidate.Runtime.HtrPayloadWithdrawalLoopMemory
import InitECandidate.Runtime.RlpSliceInputPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The entire withdrawal loop retains the concrete request pointer/length
metadata required by the final payload hashing suffix. -/
theorem htrPayload_withdrawal_loop_preserves_requests {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator zeroHashes array roots heap count payload requests length : BitVec 64) (rank : Nat)
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
    (budget : rank * (htrWithdrawalBodyCost + 2) ≤ state.clock)
    (run : evaluateHOLFiniteState state (.while htrPayloadWithdrawalCondition htrPayloadWithdrawalStep) = (none,post)) :
    RlpSliceEntry post payload (4#64) requests length := by
  have frame (watched : BitVec 64) (lo : payload.toNat ≤ watched.toNat)
      (hi : watched.toNat ≤ payload.toNat + 72) : post.memory watched = state.memory watched := by
    exact htrPayload_withdrawal_loop_normal_memory pointer accelerator zeroHashes array roots heap count watched
      countBound rootsAligned rootsFits (by omega) heapAligned heapFits (by omega) accelAligned
      (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)) state post rank code valid
      pointerGlobal accelGlobal zeroGlobal budget run
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
  have metadata := evaluateHOLFiniteState_metadata state (.while htrPayloadWithdrawalCondition htrPayloadWithdrawalStep)
  rw [run] at metadata
  exact entry.after_frame state post payload (4#64) requests length metadata.2.1 pointerFrame
    (by simpa only [BitVec.add_assoc,show (4#64) * (16#64) + (8#64) = (72#64) by decide] using lengthFrame)

#print axioms htrPayload_withdrawal_loop_preserves_requests
end InitECandidate.Runtime
