import InitECandidate.Runtime.HtrNewPayloadCallGuarded
import InitECandidate.Runtime.HtrNewPayloadBodyMemoryGuarded
import InitECandidate.Runtime.PanDiscardCallNormalResult
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem htrNewPayload_call_normal_memory_guarded {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes chunk record heap si out payload blobs blobCount parentRoot
      array count input inputLength raw rawLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength watched : BitVec 64)
    (workspace : HtrRequestsWorkspace state sha accelerator zeroHashes chunk record heap)
    (layout : ListHashMemoryLayout state sha accelerator zeroHashes chunk heap out watched)
    (decoded : HtrRequestsDecoded state record)
    (header : HtrNewPayloadHeader state si payload blobs blobCount parentRoot record)
    (payloadDecoded : HtrPayloadDecoded state payload array count input inputLength raw rawLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word si),.val (.word out)])
    (siRecord : si.toNat + 32 < record.toNat) (recordBefore : record.toNat + 72 < heap.toNat)
    (shaSi : sha.toNat + 64 ≤ si.toNat) (accelSi : accelerator.toNat + 96 ≤ si.toNat)
    (chunkSi : chunk.toNat + 32 ≤ si.toNat)
    (arrayHeap : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (chunkArray : count ≠ 0 → chunk.toNat + 32 ≤ array.toNat)
    (accelArray : count ≠ 0 → accelerator.toNat + 96 ≤ array.toNat) (shaArray : count ≠ 0 → sha.toNat + 64 ≤ array.toNat)
    (payloadHeap : payload.toNat + 72 < heap.toNat)
    (chunkPayload : chunk.toNat + 32 ≤ payload.toNat)
    (accelPayload : accelerator.toNat + 96 ≤ payload.toNat) (shaPayload : sha.toNat + 64 ≤ payload.toNat)
    (budget : htrNewPayloadBodyCost + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_new_payload_request") arguments) = (none,post)) :
    post.memory watched = state.memory watched := by
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "htr_new_payload_request") (ofString "si") (ofString "out")
    (sourceFunctionBody Guest.guestFn_htr_new_payload_request) .one si out (by decide)
    (by rw [workspace.code]; exact originalRuntimeCode_htrNewPayload_lookup)
  obtain ⟨value,output,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "htr_new_payload_request")
    .one arguments _ (sourceFunctionBody Guest.guestFn_htr_new_payload_request) _ args lookup run
  let entry := callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "si",.val (.word si))).update (ofString "out",.val (.word out)))
  have decodedEntry : HtrRequestsDecoded entry record := by
    intro index inside
    obtain ⟨p,n,old,small⟩ := decoded index inside
    exact ⟨p,n,old.after_frame state entry record index p n rfl rfl rfl,small⟩
  rw [sourceFunctionBody_eq_structural] at bodyRun
  change evaluateHOLFiniteState entry (htrNewPayloadAt 0) = (some (.returned value),output) at bodyRun
  rw [postEq]
  exact htrNewPayload_body_returned_memory_guarded entry output sha accelerator zeroHashes chunk record heap si out payload blobs blobCount parentRoot
    array count input inputLength raw rawLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength watched value
    (workspace.transfer rfl rfl) (layout.transfer rfl rfl) decodedEntry (header.after_frame rfl (fun _ _ => rfl)) (payloadDecoded.after_frame rfl rfl)
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    siRecord recordBefore shaSi accelSi chunkSi arrayHeap chunkArray accelArray shaArray payloadHeap chunkPayload accelPayload shaPayload
    (by change htrNewPayloadBodyCost ≤ state.clock - 1; exact Nat.le_sub_of_add_le budget) bodyRun

#print axioms htrNewPayload_call_normal_memory_guarded
end InitECandidate.Runtime
