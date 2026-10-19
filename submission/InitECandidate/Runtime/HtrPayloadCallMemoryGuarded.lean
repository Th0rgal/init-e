import InitECandidate.Runtime.HtrPayloadCallMemory
import InitECandidate.Runtime.HtrPayloadHeaderEntryMemoryGuarded
import InitECandidate.Runtime.HtrBytesVectorDecodedFrameGuarded
import InitECandidate.Runtime.HtrPayloadHeaderEntryMemory
import InitECandidate.Runtime.HtrPayloadUniformBound
import InitECandidate.Runtime.OriginalHtrPayloadCode
import InitECandidate.Runtime.PanDiscardCallNormalResult
import InitECandidate.Runtime.PanTwoWordShapeLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- The actual installed payload call preserves decoded outer memory outside
its output, SHA/chunk workspaces and fresh allocations. The clock premise is
the same input-uniform bound used by the payload runtime proof. -/
theorem htrPayload_call_normal_memory_guarded (pointer accelerator zeroHashes chunk array heap input inputLength count payload withdrawalArray withdrawalCount requests requestLength raw rawLength out blobs blobLength watched : BitVec 64)
    (small : inputLength.toNat ≤ 134217712) (countBound : count.toNat ≤ 134217712)
    (arrayHeap : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (chunkAligned : chunk.toNat % 8 = 0) (chunkFits : count ≠ 0 → chunk.toNat + 32 ≤ array.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : count ≠ 0 → accelerator.toNat + 96 ≤ array.toNat) (pointerFits : count ≠ 0 → pointer.toNat + 64 ≤ array.toNat)
    (payloadHeap : payload.toNat + 72 < heap.toNat)
    (chunkPayload : chunk.toNat + 32 ≤ payload.toNat)
    (accelPayload : accelerator.toNat + 96 ≤ payload.toNat) (pointerPayload : pointer.toNat + 64 ≤ payload.toNat)
    {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (layout : ListHashMemoryLayout state pointer accelerator zeroHashes chunk heap out watched)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word payload),.val (.word out)])
    (code : state.code = originalRuntimeCode)
    (pointerGlobal : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (accelGlobal : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (zeroGlobal : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (chunkGlobal : state.globals.lookup (ofString "ssz_len_chunk") = some (.val (.word chunk)))
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (transactions : RlpSliceEntry state payload (2#64) array count)
    (slices : RlpSliceInputPrefix state array input inputLength count.toNat)
    (rawEntry : RlpSliceEntry state payload (0#64) raw rawLength)
    (withdrawals : RlpSliceEntry state payload (3#64) withdrawalArray withdrawalCount)
    (withdrawalBound : withdrawalCount.toNat ≤ 134217712)
    (requestEntry : RlpSliceEntry state payload (4#64) requests requestLength)
    (requestBound : requestLength.toNat ≤ 134217712)
    (blobEntry : RlpSliceEntry state payload (1#64) blobs blobLength)
    (blobBound : blobLength.toNat ≤ 134217712)
    (budget : htrPayloadUniformCost + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_payload") arguments) = (none,post)) :
    post.memory watched = state.memory watched := by
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "htr_payload") (ofString "pl") (ofString "out")
    (sourceFunctionBody Guest.guestFn_htr_payload) .one payload out (by decide)
    (by rw [code]; exact originalRuntimeCode_htrPayload_lookup)
  obtain ⟨value,output,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "htr_payload")
    .one arguments _ (sourceFunctionBody Guest.guestFn_htr_payload) _ args lookup run
  let entry := callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "pl",.val (.word payload))).update (ofString "out",.val (.word out)))
  have cell (field p n : BitVec 64) (old : RlpSliceEntry state payload field p n) : RlpSliceEntry entry payload field p n :=
    old.after_frame state entry payload field p n rfl rfl rfl
  have nextSlices : RlpSliceInputPrefix entry array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨p,n,old⟩ := slices slot inside
    exact ⟨p,n,old.after_frame state entry array slot p n input inputLength rfl rfl rfl⟩
  have costLe := htrPayload_cost_le_uniform count withdrawalCount countBound withdrawalBound
  have bodyBudget : htrPayloadHeaderMarkCost count withdrawalCount ≤ entry.clock := by
    change htrPayloadHeaderMarkCost count withdrawalCount ≤ state.clock - 1
    exact costLe.trans (Nat.le_sub_of_add_le budget)
  have actual : evaluateHOLFiniteState entry (htrPayloadAt 0) = (some (.returned value),output) := by
    rw [sourceFunctionBody_eq_structural] at bodyRun
    exact bodyRun
  have frame := payload_header_entry_memory_guarded pointer accelerator zeroHashes chunk array heap input inputLength count payload
    withdrawalArray withdrawalCount requests requestLength raw rawLength out blobs blobLength watched small countBound arrayHeap chunkAligned chunkFits
    heapAligned heapFits accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload entry output value
    (layout.transfer rfl rfl) code pointerGlobal accelGlobal zeroGlobal chunkGlobal heapGlobal (cell _ _ _ transactions) nextSlices (cell _ _ _ rawEntry)
    (by simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (cell _ _ _ withdrawals) withdrawalBound (cell _ _ _ requestEntry) requestBound (cell _ _ _ blobEntry) blobBound bodyBudget actual
  rw [postEq]
  exact frame

#print axioms htrPayload_call_normal_memory_guarded
end InitECandidate.Runtime
