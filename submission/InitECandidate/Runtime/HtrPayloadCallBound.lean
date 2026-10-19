import InitECandidate.Runtime.HtrPayloadUniformBound
import InitECandidate.Runtime.OriginalHtrPayloadCode
import InitECandidate.Runtime.PanTwoWordShapeLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- The actual installed payload call takes at most the uniform body bound
plus its call tick, with all metadata and geometry read from the caller state. -/
theorem runBounded_htrPayload_call (pointer accelerator zeroHashes chunk array heap input inputLength count payload withdrawalArray withdrawalCount requests requestLength raw rawLength out blobs blobLength : BitVec 64)
    (small : inputLength.toNat ≤ 134217712) (countBound : count.toNat ≤ 134217712)
    (arrayHeap : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (chunkAligned : chunk.toNat % 8 = 0) (chunkFits : chunk.toNat + 32 ≤ array.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ array.toNat) (pointerFits : pointer.toNat + 64 ≤ array.toNat)
    (payloadHeap : payload.toNat + 72 < heap.toNat)
    (chunkPayload : chunk.toNat + 32 ≤ payload.toNat)
    (accelPayload : accelerator.toNat + 96 ≤ payload.toNat) (pointerPayload : pointer.toNat + 64 ≤ payload.toNat)
    {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS))
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
    (budget : htrPayloadUniformCost + 1 ≤ state.clock) :
    RunBounded state (.call (some (destination,none)) (ofString "htr_payload") arguments) (htrPayloadUniformCost + 1) := by
  refine RunBounded.call args budget ?_
  intro body locals returnShape lookup
  rw [pan_two_word_lookup_shape state.code.lookup (ofString "htr_payload") (ofString "pl") (ofString "out")
    (sourceFunctionBody Guest.guestFn_htr_payload) .one payload out (by decide)
    (by rw [code]; exact originalRuntimeCode_htrPayload_lookup)] at lookup
  cases lookup
  let entry := callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "pl",.val (.word payload))).update (ofString "out",.val (.word out)))
  have cell (field p n : BitVec 64) (old : RlpSliceEntry state payload field p n) : RlpSliceEntry entry payload field p n :=
    old.after_frame state entry payload field p n rfl rfl rfl
  have nextSlices : RlpSliceInputPrefix entry array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨p,n,old⟩ := slices slot inside
    exact ⟨p,n,old.after_frame state entry array slot p n input inputLength rfl rfl rfl⟩
  rw [sourceFunctionBody_eq_structural]
  change RunBounded entry (htrPayloadAt 0) htrPayloadUniformCost
  exact payload_header_entry_uniform_bound pointer accelerator zeroHashes chunk array heap input inputLength count payload
    withdrawalArray withdrawalCount requests requestLength raw rawLength out blobs blobLength small countBound arrayHeap chunkAligned chunkFits
    heapAligned heapFits accelAligned accelFits pointerFits payloadHeap chunkPayload accelPayload pointerPayload entry code
    pointerGlobal accelGlobal zeroGlobal chunkGlobal heapGlobal (cell _ _ _ transactions) nextSlices (cell _ _ _ rawEntry)
    (by simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (cell _ _ _ withdrawals) withdrawalBound (cell _ _ _ requestEntry) requestBound (cell _ _ _ blobEntry) blobBound
    (by change htrPayloadUniformCost ≤ state.clock - 1; exact Nat.le_sub_of_add_le budget)

#print axioms runBounded_htrPayload_call
end InitECandidate.Runtime
