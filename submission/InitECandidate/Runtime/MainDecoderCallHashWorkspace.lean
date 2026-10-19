import InitECandidate.Runtime.MainDecoderCallHashEntry
import InitECandidate.Runtime.MainDecoderHashWorkspaceGlobals
import InitECandidate.Runtime.HtrRequestsBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- The complete decoded hash metadata and actual final heap agree with the
payload and array extents exported by the execution-linked decoder result. -/
theorem main_decoder_call_hash_workspace {F : Type} (state ready post : PanSemStateFiniteExact 64 F)
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
      (count = 0 ∨ payload.toNat + 136 ≤ array.toNat) ∧
      2713715344 ≤ heap.toNat ∧
      HtrRequestsWorkspace post 2713714688 2713714880 2713715408 2713715312 record finalHeap := by
  obtain ⟨finalHeap,heap,payload,blobs,blobCount,parentRoot,record,array,count,input,inputLength,withdrawals,withdrawalCount,
      requests,requestLength,payloadBlobs,blobLength,binding,growth,header,table,recordAfter,decoded,finalBinding,recordExtent,
      cap,alignment,payloadExtent,arrayExtent,si,origin⟩ := main_decoder_call_hash_entry state ready post code arena valid run
  obtain ⟨sha,accel,chunk,zero⟩ := main_decoder_hash_workspace_globals state ready post code arena valid run
  obtain ⟨length,out,z,entryHeap,inp,output,z32,small,fits,offsets,entryBinding,entryCap,entryAligned,lower,installed,domain,si0,err⟩ := valid.fields
  have same : entryHeap = heap := by simpa using entryBinding.symm.trans binding
  subst entryHeap
  have metadata := evaluateHOLFiniteState_metadata ready mainStatelessCall
  rw [run] at metadata
  have postCode : post.code = originalRuntimeCode := metadata.1.trans (installed.trans code)
  have workspace : HtrRequestsWorkspace post 2713714688 2713714880 2713715408 2713715312 record finalHeap :=
    ⟨sha,accel,zero,chunk,finalBinding,alignment,cap,(by omega),(by decide),(by decide),
      (by change 2713714752 ≤ record.toNat; omega),
      (by change 2713714976 ≤ record.toNat; omega),
      (by change 2713715344 ≤ record.toNat; omega),postCode⟩
  exact ⟨finalHeap,heap,payload,blobs,blobCount,parentRoot,record,array,count,input,inputLength,withdrawals,withdrawalCount,
    requests,requestLength,payloadBlobs,blobLength,binding,growth,header,table,recordAfter,decoded,finalBinding,recordExtent,
    cap,alignment,payloadExtent,arrayExtent,si,origin,(by omega),workspace⟩

#print axioms main_decoder_call_hash_workspace
end InitECandidate.Runtime
