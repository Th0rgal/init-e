import InitECandidate.Runtime.MainDecoderCallHashWorkspace
import InitECandidate.Runtime.MainInitialHashReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- After the actual main decoder returns, the original root allocation and
initial hash reach VM validation within a finite uniform cost or abort. All
hash layout and metadata premises are derived from that decoder execution. -/
theorem main_decoder_initial_hash_reaches {F : Type} (state ready decodedState : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 →
      2713714688 ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (valid : MainDecoderEntry state ready)
    (run : evaluateHOLFiniteState ready mainStatelessCall = (none,decodedState))
    (budget : 2 + (htrNewPayloadBodyCost + 1) ≤ decodedState.clock) :
    ∃ rootHeap : BitVec 64, Reaches decodedState (mainAt 21)
      (fun post => ∃ rootReady, AllocationDeclarationReady decodedState (ofString "root") rootHeap 32 rootReady ∧
        evaluateHOLFiniteState rootReady mainInitialHashCall = (none,post))
      (2 + (htrNewPayloadBodyCost + 1)) (mainAt 23) := by
  obtain ⟨finalHeap,heap,payload,blobs,blobCount,parentRoot,record,array,count,input,inputLength,withdrawals,withdrawalCount,
      requests,requestLength,payloadBlobs,blobLength,binding,growth,header,table,recordAfter,decoded,finalBinding,recordExtent,
      cap,alignment,payloadExtent,arrayExtent,si,origin,lower,workspace⟩ :=
    main_decoder_call_hash_workspace state ready decodedState code arena valid run
  exact ⟨finalHeap,main_root_initial_hash_reaches decodedState finalHeap heap payload blobs blobCount parentRoot record array count
    input inputLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength workspace si header table decoded
    lower growth recordAfter payloadExtent arrayExtent origin budget⟩

#print axioms main_decoder_initial_hash_reaches
end InitECandidate.Runtime
