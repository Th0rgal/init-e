import InitECandidate.Runtime.MainInitialHashCallBound
import InitECandidate.Runtime.RunBoundedSeqReach
import InitECandidate.Runtime.NormalRelLocalCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- Main's root allocation and installed initial hash reach the actual VM
validation continuation within a finite uniform cost or abort earlier. -/
theorem main_root_initial_hash_reaches {F : Type} (state : PanSemStateFiniteExact 64 F)
    (heap si payload blobs blobCount parentRoot record array count input inputLength
      withdrawals withdrawalCount requests requestLength payloadBlobs blobLength : BitVec 64)
    (workspace : HtrRequestsWorkspace state 2713714688 2713714880 2713715408 2713715312 record heap)
    (atSi : state.locals.lookup (ofString "si") = some (.val (.word si)))
    (header : HtrNewPayloadHeader state si payload blobs blobCount parentRoot record)
    (table : HtrRequestsDecoded state record)
    (decoded : HtrPayloadDecoded state payload array count input inputLength input inputLength
      withdrawals withdrawalCount requests requestLength payloadBlobs blobLength)
    (siLower : 2713715344 ≤ si.toNat)
    (payloadAfter : si.toNat + 96 ≤ payload.toNat)
    (siRecord : si.toNat + 32 < record.toNat)
    (payloadExtent : payload.toNat + 136 ≤ heap.toNat)
    (arrayExtent : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (origin : count = 0 ∨ payload.toNat + 136 ≤ array.toNat)
    (budget : 2 + (htrNewPayloadBodyCost + 1) ≤ state.clock) :
    Reaches state (mainAt 21)
      (fun post => ∃ rootReady, AllocationDeclarationReady state (ofString "root") heap 32 rootReady ∧
        evaluateHOLFiniteState rootReady mainInitialHashCall = (none,post))
      (2 + (htrNewPayloadBodyCost + 1)) (mainAt 23) := by
  have root := main_root_allocation_reaches state heap workspace.code workspace.atHeap workspace.heapFits (by omega)
  have rootWithClock : Reaches state (mainAt 21)
      (fun next => AllocationDeclarationReady state (ofString "root") heap 32 next ∧ state.clock ≤ next.clock + 2)
      2 (mainAt 22) := by
    rcases root with ⟨next,allocation,spent,remaining,agreement⟩ | aborted
    · exact Or.inl ⟨next,⟨allocation,spent⟩,spent,remaining,agreement⟩
    · exact Or.inr aborted
  apply reaches_trans state (mainAt 21) (mainAt 22) (mainAt 23) _ _ 2 (htrNewPayloadBodyCost + 1) rootWithClock
  intro next facts
  obtain ⟨allocation,spent⟩ := facts
  have callBound := main_initial_hash_after_root_bounded state next heap si payload blobs blobCount parentRoot record array count
    input inputLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength workspace atSi header table decoded
    siLower payloadAfter siRecord payloadExtent arrayExtent origin allocation (by omega)
  rw [source_main_initial_hash_call]
  apply runBounded_seq_reaches next mainInitialHashCall (mainAt 23) _ (htrNewPayloadBodyCost + 1) callBound
  · intro value
    exact discard_call_not_returned next (ofString "htr_new_payload_request")
      [.var .local (ofString "si"),.var .local (ofString "root")] value
  · intro post run
    exact ⟨next,allocation,run⟩

#print axioms main_root_initial_hash_reaches
end InitECandidate.Runtime
