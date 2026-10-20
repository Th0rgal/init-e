import InitECandidate.Runtime.MainDecoderCallHeapUpper
import InitECandidate.Runtime.MainDecoderCallHashWorkspace
import InitECandidate.Runtime.MainInitialHashReachMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- After the actual main decoder returns, the original root allocation and
initial hash reach VM validation within a finite uniform cost or abort. All
hash layout and metadata premises are derived from that decoder execution. -/
theorem main_decoder_vm_entry_reaches_heap_upper {F : Type} (state ready decodedState : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 →
      2713714688 ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (valid : MainDecoderEntry state ready)
    (run : evaluateHOLFiniteState ready mainStatelessCall = (none,decodedState))
    (budget : 2 + (htrNewPayloadBodyCost + 1) ≤ decodedState.clock) :
    ∃ rootHeap si payload blobs blobCount parentRoot record array count input inputLength withdrawals withdrawalCount
      requests requestLength payloadBlobs blobLength : BitVec 64,
      rootHeap.toNat ≤ 5000000000 ∧ Reaches decodedState (mainAt 21)
      (fun post => HtrNewPayloadHeader post si payload blobs blobCount parentRoot record ∧
        HtrRequestsDecoded post record ∧
        HtrPayloadDecoded post payload array count input inputLength input inputLength
          withdrawals withdrawalCount requests requestLength payloadBlobs blobLength ∧
        post.locals.lookup (ofString "si") = some (.val (.word si)) ∧
        post.locals.lookup (ofString "root") = some (.val (.word rootHeap)) ∧
        post.globals = (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word (allocationEnd rootHeap 32))) decodedState).globals ∧
        post.memaddrs = decodedState.memaddrs ∧ post.code = originalRuntimeCode ∧
        (∀ watched : BitVec 64, 2713715344 ≤ watched.toNat → watched.toNat < rootHeap.toNat →
          post.memory watched = decodedState.memory watched))
      (2 + (htrNewPayloadBodyCost + 1)) (mainAt 23) := by
  obtain ⟨finalHeap,heap,payload,blobs,blobCount,parentRoot,record,array,count,input,inputLength,withdrawals,withdrawalCount,
      requests,requestLength,payloadBlobs,blobLength,binding,growth,header,table,recordAfter,decoded,finalBinding,recordExtent,
      cap,alignment,payloadExtent,arrayExtent,si,origin,lower,workspace⟩ :=
    main_decoder_call_hash_workspace state ready decodedState code arena valid run
  obtain ⟨_,_,upperHeap,_,_,_,_,upperBinding,_,_,upper,_⟩ :=
    main_decoder_call_heap_upper state ready decodedState code arena valid run
  have sameHeap : upperHeap=finalHeap := by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using upperBinding.symm.trans finalBinding
  subst upperHeap
  exact ⟨finalHeap,heap,payload,blobs,blobCount,parentRoot,record,array,count,input,inputLength,withdrawals,withdrawalCount,
    requests,requestLength,payloadBlobs,blobLength,upper,main_root_initial_hash_reaches_metadata decodedState finalHeap heap payload blobs blobCount parentRoot record array count
    input inputLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength workspace si header table decoded
    lower growth recordAfter payloadExtent arrayExtent origin budget⟩

#print axioms main_decoder_vm_entry_reaches_heap_upper
end InitECandidate.Runtime
