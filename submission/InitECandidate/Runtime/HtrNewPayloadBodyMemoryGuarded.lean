import InitECandidate.Runtime.HtrNewPayloadBodyGuarded
import InitECandidate.Runtime.HtrNewPayloadAllocationMemoryGuarded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem htrNewPayload_body_returned_memory_guarded {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes chunk record heap si out payload blobs blobCount parentRoot
      array count input inputLength raw rawLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength watched : BitVec 64) (value : ValueHOL 64)
    (workspace : HtrRequestsWorkspace state sha accelerator zeroHashes chunk record heap)
    (layout : ListHashMemoryLayout state sha accelerator zeroHashes chunk heap out watched)
    (decoded : HtrRequestsDecoded state record)
    (header : HtrNewPayloadHeader state si payload blobs blobCount parentRoot record)
    (payloadDecoded : HtrPayloadDecoded state payload array count input inputLength raw rawLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength)
    (atSi : state.locals.lookup (ofString "si") = some (.val (.word si)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (siRecord : si.toNat + 32 < record.toNat) (recordBefore : record.toNat + 72 < heap.toNat)
    (shaSi : sha.toNat + 64 ≤ si.toNat) (accelSi : accelerator.toNat + 96 ≤ si.toNat)
    (chunkSi : chunk.toNat + 32 ≤ si.toNat)
    (arrayHeap : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (chunkArray : count ≠ 0 → chunk.toNat + 32 ≤ array.toNat)
    (accelArray : count ≠ 0 → accelerator.toNat + 96 ≤ array.toNat) (shaArray : count ≠ 0 → sha.toNat + 64 ≤ array.toNat)
    (payloadHeap : payload.toNat + 72 < heap.toNat)
    (chunkPayload : chunk.toNat + 32 ≤ payload.toNat)
    (accelPayload : accelerator.toNat + 96 ≤ payload.toNat) (shaPayload : sha.toNat + 64 ≤ payload.toNat)
    (budget : htrNewPayloadBodyCost ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrNewPayloadAt 0) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  change 1 + htrNewPayloadAllocationCost ≤ state.clock at budget
  have reached := evaluate_heapMark_declaration_reaches state (ofString "mark") heap (htrNewPayloadAt 1)
    workspace.code workspace.atHeap (by omega)
  rw [← source_htrNewPayload_mark] at reached
  obtain ⟨next,facts,spent,_,agreement,normal⟩ := reaches_returned_continuation state (htrNewPayloadAt 0) (htrNewPayloadAt 1)
    _ 1 value reached (by rw [run])
  obtain ⟨locals,memory,globals,installed,domain⟩ := facts
  have keep (key : MlS) (different : key ≠ ofString "mark") : next.locals.lookup key = state.locals.lookup key := by
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have decodedNext : HtrRequestsDecoded next record := by
    intro index inside
    obtain ⟨p,n,entry,small⟩ := decoded index inside
    exact ⟨p,n,entry.after_frame state next record index p n domain (congrFun memory _) (congrFun memory _),small⟩
  have remaining : htrNewPayloadAllocationCost ≤ next.clock := by omega
  have suffix := htrNewPayload_allocation_returned_memory_guarded next (evaluateHOLFiniteState next (htrNewPayloadAt 1)).2
    sha accelerator zeroHashes chunk record heap si out payload blobs blobCount parentRoot
    array count input inputLength raw rawLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength heap watched value
    (workspace.transfer globals installed) (layout.transfer globals installed)
    (by rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]) decodedNext (header.after_frame domain (fun _ _ => congrFun memory _))
    (payloadDecoded.after_frame domain memory) ((keep _ (by decide)).trans atSi) ((keep _ (by decide)).trans atOut)
    siRecord recordBefore shaSi accelSi chunkSi arrayHeap chunkArray accelArray shaArray payloadHeap chunkPayload accelPayload shaPayload remaining
    (Prod.ext normal rfl)
  have outputMemory : post.memory = (evaluateHOLFiniteState next (htrNewPayloadAt 1)).2.memory := by
    have same := agreement.2.2.1
    rw [run] at same
    exact same
  rw [outputMemory,suffix]
  exact congrFun memory watched

#print axioms htrNewPayload_body_returned_memory_guarded
end InitECandidate.Runtime
