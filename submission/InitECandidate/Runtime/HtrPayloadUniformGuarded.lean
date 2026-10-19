import InitECandidate.Runtime.HtrPayloadUniformBound
import InitECandidate.Runtime.HtrPayloadHeaderEntryGuarded
import InitECandidate.Runtime.HtrBytesVectorDecodedFrameGuarded
import InitECandidate.Runtime.HtrPayloadHeaderEntryBound
namespace InitECandidate.Runtime
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A uniform payload bound obtained from the challenge input/count bound. -/
theorem htrPayload_cost_le_uniform_guarded (count withdrawalCount : BitVec 64)
    (countBound : count.toNat ≤ 134217712) (withdrawalBound : withdrawalCount.toNat ≤ 134217712) :
    htrPayloadHeaderMarkCost count withdrawalCount ≤ htrPayloadUniformCost := by
  have tx := Nat.mul_le_mul_right (htrPbytesBodyCost + 2) countBound
  have wd := Nat.mul_le_mul_right (htrWithdrawalBodyCost + 2) withdrawalBound
  simp only [htrPayloadUniformCost,htrPayloadHeaderMarkCost,htrPayloadHeaderAllocationCost,
    htrPayloadHeaderCost4,htrPayloadHeaderCost5,htrPayloadHeaderCost6,htrPayloadHeaderCost7,htrPayloadHeaderCost8,
    htrPayloadHeaderCost9,htrPayloadHeaderCost10,htrPayloadHeaderCost11,htrPayloadHeaderCost12,htrPayloadHeaderCost13,
    htrPayloadTxMetadataCost,htrPayloadWithdrawalTotalCost]
  simp only [show (134217712#64).toNat = 134217712 by decide]
  generalize htrPbytesBodyCost = pc at *
  generalize htrWithdrawalBodyCost = wc at *
  generalize htrPlistChunksCost = lc at *
  generalize htrPayloadPostWithdrawalCost = tc at *
  generalize htrBytesListBodyCost = bc at *
  generalize htrBytesVectorBodyCost = vc at *
  omega

theorem payload_header_entry_uniform_bound_guarded : PayloadHeaderEntryBoundGuarded (fun _ _ => htrPayloadUniformCost) := by
  intro pointer accelerator zeroHashes chunk array heap input inputLength count payload withdrawalArray withdrawalCount
    requests requestLength raw rawLength out blobs blobLength small countBound arrayHeap chunkAligned chunkFits heapAligned heapFits
    accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload F state
    code pointerGlobal accelGlobal zeroGlobal chunkGlobal heapGlobal transactions slices rawEntry outLocal payloadLocal
    withdrawals withdrawalBound requestEntry requestBound blobEntry blobBound budget
  have le := htrPayload_cost_le_uniform_guarded count withdrawalCount countBound withdrawalBound
  exact (payload_header_entry_bound_guarded pointer accelerator zeroHashes chunk array heap input inputLength count payload
    withdrawalArray withdrawalCount requests requestLength raw rawLength out blobs blobLength small countBound arrayHeap chunkAligned chunkFits
    heapAligned heapFits accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload state code pointerGlobal
    accelGlobal zeroGlobal chunkGlobal heapGlobal transactions slices rawEntry outLocal payloadLocal withdrawals withdrawalBound
    requestEntry requestBound blobEntry blobBound (le.trans budget)).weaken le

#print axioms htrPayload_cost_le_uniform_guarded
#print axioms payload_header_entry_uniform_bound_guarded
end InitECandidate.Runtime
