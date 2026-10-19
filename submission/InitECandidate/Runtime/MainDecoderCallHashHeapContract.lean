import InitECandidate.Runtime.MainDecoderCallHashContract
import InitECandidate.Runtime.MainDecoderCallRequestHeapExtent
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The combined hash input contract refers to the actual final heap and its
full request-record extent, with record identity read from the outer header. -/
theorem main_decoder_call_hash_heap_contract {F : Type} (state ready post : PanSemStateFiniteExact 64 F)
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
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧ record.toNat + 80 ≤ finalHeap.toNat := by
  obtain ⟨heap,payload,blobs,blobCount,parentRoot,record,array,count,input,inputLength,withdrawals,withdrawalCount,
      requests,requestLength,payloadBlobs,blobLength,binding,growth,header,table,recordAfter,decoded⟩ :=
    main_decoder_call_hash_contract state ready post code arena valid run
  obtain ⟨_,otherHeap,otherRecord,_,otherBinding,_,_,pointer,_,finalHeap,finalBinding,extent⟩ :=
    main_decoder_call_request_heap_extent state ready post code arena valid run
  have sameHeap : otherHeap = heap := by simpa using otherBinding.symm.trans binding
  subst otherHeap
  have sameRecord : otherRecord = record := by simpa using pointer.symm.trans header.requestsCell
  subst otherRecord
  exact ⟨finalHeap,heap,payload,blobs,blobCount,parentRoot,record,array,count,input,inputLength,withdrawals,withdrawalCount,
    requests,requestLength,payloadBlobs,blobLength,binding,growth,header,table,recordAfter,decoded,finalBinding,extent⟩

#print axioms main_decoder_call_hash_heap_contract
end InitECandidate.Runtime
