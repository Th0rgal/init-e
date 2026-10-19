import InitECandidate.Runtime.HtrNewPayloadCallBound
import InitECandidate.Runtime.HtrNewPayloadBodyGuarded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem runBounded_htrNewPayload_call_guarded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes chunk record heap si out payload blobs blobCount parentRoot
      array count input inputLength raw rawLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength : BitVec 64)
    (workspace : HtrRequestsWorkspace state sha accelerator zeroHashes chunk record heap)
    (decoded : HtrRequestsDecoded state record)
    (header : HtrNewPayloadHeader state si payload blobs blobCount parentRoot record)
    (payloadDecoded : HtrPayloadDecoded state payload array count input inputLength raw rawLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
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
    (budget : htrNewPayloadBodyCost + 1 ≤ state.clock) :
    RunBounded state (.call (some (destination,none)) (ofString "htr_new_payload_request") arguments) (htrNewPayloadBodyCost + 1) := by
  refine RunBounded.call args budget ?_
  intro body locals returnShape lookup
  rw [pan_two_word_lookup_shape state.code.lookup (ofString "htr_new_payload_request") (ofString "si") (ofString "out")
    (sourceFunctionBody Guest.guestFn_htr_new_payload_request) .one si out (by decide)
    (by rw [workspace.code]; exact originalRuntimeCode_htrNewPayload_lookup)] at lookup
  cases lookup
  let entry := callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "si",.val (.word si))).update (ofString "out",.val (.word out)))
  have decodedEntry : HtrRequestsDecoded entry record := by
    intro index inside
    obtain ⟨p,n,old,small⟩ := decoded index inside
    exact ⟨p,n,old.after_frame state entry record index p n rfl rfl rfl,small⟩
  rw [sourceFunctionBody_eq_structural]
  change RunBounded entry (htrNewPayloadAt 0) htrNewPayloadBodyCost
  exact runBounded_htrNewPayload_body_guarded entry sha accelerator zeroHashes chunk record heap si out payload blobs blobCount parentRoot
    array count input inputLength raw rawLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength
    (workspace.transfer rfl rfl) decodedEntry (header.after_frame rfl (fun _ _ => rfl)) (payloadDecoded.after_frame rfl rfl)
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    siRecord recordBefore shaSi accelSi chunkSi arrayHeap chunkArray accelArray shaArray payloadHeap chunkPayload accelPayload shaPayload
    (by change htrNewPayloadBodyCost ≤ state.clock - 1; exact Nat.le_sub_of_add_le budget)

#print axioms runBounded_htrNewPayload_call_guarded
end InitECandidate.Runtime
