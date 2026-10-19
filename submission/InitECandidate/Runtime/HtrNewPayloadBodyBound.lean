import InitECandidate.Runtime.HtrNewPayloadAllocationBound
import InitECandidate.Runtime.HeapMarkDeclarationReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def htrNewPayloadBodyCost : Nat := 1 + htrNewPayloadAllocationCost

/-- All outcomes of the original new-payload hash body are bounded, including
allocation failure, from the concrete decoded input and workspace geometry. -/
theorem runBounded_htrNewPayload_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes chunk record heap si out payload blobs blobCount parentRoot
      array count input inputLength raw rawLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength : BitVec 64)
    (workspace : HtrRequestsWorkspace state sha accelerator zeroHashes chunk record heap)
    (decoded : HtrRequestsDecoded state record)
    (header : HtrNewPayloadHeader state si payload blobs blobCount parentRoot record)
    (payloadDecoded : HtrPayloadDecoded state payload array count input inputLength raw rawLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength)
    (atSi : state.locals.lookup (ofString "si") = some (.val (.word si)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (siRecord : si.toNat + 32 < record.toNat) (recordBefore : record.toNat + 72 < heap.toNat)
    (shaSi : sha.toNat + 64 ≤ si.toNat) (accelSi : accelerator.toNat + 96 ≤ si.toNat)
    (chunkSi : chunk.toNat + 32 ≤ si.toNat)
    (arrayHeap : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (chunkArray : chunk.toNat + 32 ≤ array.toNat)
    (accelArray : accelerator.toNat + 96 ≤ array.toNat) (shaArray : sha.toNat + 64 ≤ array.toNat)
    (payloadHeap : payload.toNat + 72 < heap.toNat)
    (chunkPayload : chunk.toNat + 32 ≤ payload.toNat)
    (accelPayload : accelerator.toNat + 96 ≤ payload.toNat) (shaPayload : sha.toNat + 64 ≤ payload.toNat)
    (budget : htrNewPayloadBodyCost ≤ state.clock) :
    RunBounded state (htrNewPayloadAt 0) htrNewPayloadBodyCost := by
  change 1 + htrNewPayloadAllocationCost ≤ state.clock at budget
  have reached := evaluate_heapMark_declaration_reaches state (ofString "mark") heap (htrNewPayloadAt 1)
    workspace.code workspace.atHeap (by omega)
  rw [← source_htrNewPayload_mark] at reached
  exact evaluate_reaches_terminal_bounded state (htrNewPayloadAt 0) (htrNewPayloadAt 1) _ 1 _ budget reached (by
    intro next facts remaining
    obtain ⟨locals,memory,globals,installed,domain⟩ := facts
    have keep (key : MlS) (different : key ≠ ofString "mark") : next.locals.lookup key = state.locals.lookup key := by
      rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
    have decodedNext : HtrRequestsDecoded next record := by
      intro index inside
      obtain ⟨p,n,entry,small⟩ := decoded index inside
      exact ⟨p,n,entry.after_frame state next record index p n domain (congrFun memory _) (congrFun memory _),small⟩
    exact runBounded_htrNewPayload_allocation next sha accelerator zeroHashes chunk record heap si out payload blobs blobCount parentRoot
      array count input inputLength raw rawLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength
      (workspace.transfer globals installed) decodedNext (header.after_frame domain (fun _ _ => congrFun memory _))
      (payloadDecoded.after_frame domain memory) ((keep _ (by decide)).trans atSi) ((keep _ (by decide)).trans atOut)
      siRecord recordBefore shaSi accelSi chunkSi arrayHeap chunkArray accelArray shaArray payloadHeap chunkPayload accelPayload shaPayload remaining)

#print axioms runBounded_htrNewPayload_body
end InitECandidate.Runtime
