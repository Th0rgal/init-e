import InitECandidate.Runtime.MainDecoderCallHashGeometry
import InitECandidate.Runtime.MainDecoderCallReturnedHeap
import InitECandidate.Runtime.StatelessReturnedArrayOrigin
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete decoded hash metadata and actual final heap agree with the
payload and array extents exported by the execution-linked decoder result. -/
theorem main_decoder_call_hash_entry {F : Type} (state ready post : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 →
      2713714688 ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (valid : MainDecoderEntry state ready)
    (run : evaluateHOLFiniteState ready mainStatelessCall = (none,post)) :
    ∃ finalHeap heap payload blobs blobCount parentRoot record array count input inputLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength : BitVec 64,
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧ heap.toNat + 96 ≤ payload.toNat ∧
      HtrNewPayloadHeader post heap payload blobs blobCount parentRoot record ∧ HtrRequestsDecoded post record ∧
      heap.toNat + 32 < record.toNat ∧
      HtrPayloadDecoded post payload array count input inputLength input inputLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧ record.toNat + 80 ≤ finalHeap.toNat ∧
      finalHeap.toNat ≤ 33806089496 ∧ finalHeap.toNat % 8 = 0 ∧
      payload.toNat + 136 ≤ finalHeap.toNat ∧ array.toNat + count.toNat * 16 ≤ finalHeap.toNat ∧
      post.locals.lookup (ofString "si") = some (.val (.word heap)) ∧
      (count = 0 ∨ payload.toNat + 136 ≤ array.toNat) := by
  obtain ⟨finalHeap,heap,payload,blobs,blobCount,parentRoot,record,array,count,input,inputLength,withdrawals,withdrawalCount,
      requests,requestLength,payloadBlobs,blobLength,binding,growth,header,table,recordAfter,decoded,finalBinding,recordExtent,
      cap,alignment,payloadExtent,arrayExtent⟩ := main_decoder_call_hash_geometry state ready post code arena valid run
  obtain ⟨length,actualHeap,actualBinding,_,_,locals,returned,_⟩ :=
    main_decoder_call_returned_heap state ready post code arena valid run
  have same : actualHeap = heap := by simpa using actualBinding.symm.trans binding
  subst actualHeap
  have si : post.locals.lookup (ofString "si") = some (.val (.word heap)) := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have origin := returned.array_origin ready post 2713731432 length 2713715344 heap payload array count
    header.payloadCell decoded.transactions.pointerCell (by simpa [BitVec.add_assoc] using decoded.transactions.lengthCell)
  exact ⟨finalHeap,heap,payload,blobs,blobCount,parentRoot,record,array,count,input,inputLength,withdrawals,withdrawalCount,
    requests,requestLength,payloadBlobs,blobLength,binding,growth,header,table,recordAfter,decoded,finalBinding,recordExtent,
    cap,alignment,payloadExtent,arrayExtent,si,origin⟩

#print axioms main_decoder_call_hash_entry
end InitECandidate.Runtime
