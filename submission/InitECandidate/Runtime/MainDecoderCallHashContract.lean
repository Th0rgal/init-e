import InitECandidate.Runtime.MainDecoderCallHashDecoded
import InitECandidate.Runtime.MainDecoderCallHashHeader
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Both decoder contracts describe the same outer record and payload: their
identities follow from the actual entry heap binding and stored payload word. -/
theorem main_decoder_call_hash_contract {F : Type} (state ready post : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 →
      2713714688 ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (valid : MainDecoderEntry state ready)
    (run : evaluateHOLFiniteState ready mainStatelessCall = (none,post)) :
    ∃ heap payload blobs blobCount parentRoot record array count input inputLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength : BitVec 64,
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧ heap.toNat + 96 ≤ payload.toNat ∧
      HtrNewPayloadHeader post heap payload blobs blobCount parentRoot record ∧ HtrRequestsDecoded post record ∧
      heap.toNat + 32 < record.toNat ∧
      HtrPayloadDecoded post payload array count input inputLength input inputLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength := by
  obtain ⟨length,heap,payload,array,count,input,inputLength,withdrawals,withdrawalCount,requests,requestLength,payloadBlobs,blobLength,
      _,binding,growth,pointer,decoded⟩ := main_decoder_call_hash_decoded state ready post code arena valid run
  obtain ⟨_,otherHeap,otherPayload,blobs,blobCount,parentRoot,record,_,otherBinding,header,requestTable,recordAfter⟩ :=
    main_decoder_call_hash_header state ready post code arena valid run
  have sameHeap : otherHeap = heap := by simpa using otherBinding.symm.trans binding
  subst otherHeap
  have samePayload : otherPayload = payload := by simpa using header.payloadCell.symm.trans pointer
  subst otherPayload
  exact ⟨heap,payload,blobs,blobCount,parentRoot,record,array,count,input,inputLength,withdrawals,withdrawalCount,
    requests,requestLength,payloadBlobs,blobLength,binding,growth,header,requestTable,recordAfter,decoded⟩

#print axioms main_decoder_call_hash_contract
end InitECandidate.Runtime
