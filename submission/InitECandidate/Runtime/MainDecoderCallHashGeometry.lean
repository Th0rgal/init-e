import InitECandidate.Runtime.MainDecoderCallHashHeapContract
import InitECandidate.Runtime.MainDecoderCallFinalGeometry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete decoded hash metadata and actual final heap agree with the
payload and array extents exported by the execution-linked decoder result. -/
theorem main_decoder_call_hash_geometry {F : Type} (state ready post : PanSemStateFiniteExact 64 F)
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
      payload.toNat + 136 ≤ finalHeap.toNat ∧ array.toNat + count.toNat * 16 ≤ finalHeap.toNat := by
  obtain ⟨finalHeap,heap,payload,blobs,blobCount,parentRoot,record,array,count,input,inputLength,withdrawals,withdrawalCount,
      requests,requestLength,payloadBlobs,blobLength,binding,growth,header,table,recordAfter,decoded,finalBinding,recordExtent⟩ :=
    main_decoder_call_hash_heap_contract state ready post code arena valid run
  obtain ⟨otherHeap,otherFinal,otherBinding,otherFinalBinding,cap,alignment,geometry⟩ :=
    main_decoder_call_final_geometry state ready post code arena valid run
  have sameHeap : otherHeap = heap := by simpa using otherBinding.symm.trans binding
  subst otherHeap
  have sameFinal : otherFinal = finalHeap := by simpa using otherFinalBinding.symm.trans finalBinding
  subst otherFinal
  have payloadGeometry := geometry payload header.payloadCell
  have arrayGeometry := payloadGeometry.2 array count decoded.transactions.pointerCell
    (by simpa [BitVec.add_assoc] using decoded.transactions.lengthCell)
  exact ⟨finalHeap,heap,payload,blobs,blobCount,parentRoot,record,array,count,input,inputLength,withdrawals,withdrawalCount,
    requests,requestLength,payloadBlobs,blobLength,binding,growth,header,table,recordAfter,decoded,finalBinding,recordExtent,
    cap,alignment,payloadGeometry.1,arrayGeometry⟩

#print axioms main_decoder_call_hash_geometry
end InitECandidate.Runtime
