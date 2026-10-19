import InitECandidate.Runtime.MainRootAllocationReach
import InitECandidate.Runtime.HtrNewPayloadAllocationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Main's actual root-buffer declaration retains the complete decoder hash
contract. Allocation failure terminates through the original allocator path. -/
theorem main_hash_root_allocation_reaches {F : Type} (state : PanSemStateFiniteExact 64 F)
    (heap si payload blobs blobCount parentRoot record array count input inputLength raw rawLength
      withdrawals withdrawalCount requests requestLength payloadBlobs blobLength : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (capped : heap.toNat ≤ 33806089496)
    (atSi : state.locals.lookup (ofString "si") = some (.val (.word si)))
    (header : HtrNewPayloadHeader state si payload blobs blobCount parentRoot record)
    (table : HtrRequestsDecoded state record)
    (decoded : HtrPayloadDecoded state payload array count input inputLength raw rawLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength)
    (budget : 2 ≤ state.clock) :
    Reaches state (mainAt 21)
      (fun next => AllocationDeclarationReady state (ofString "root") heap 32 next ∧
        next.locals.lookup (ofString "root") = some (.val (.word heap)) ∧
        next.locals.lookup (ofString "si") = some (.val (.word si)) ∧
        HtrNewPayloadHeader next si payload blobs blobCount parentRoot record ∧ HtrRequestsDecoded next record ∧
        HtrPayloadDecoded next payload array count input inputLength raw rawLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength)
      2 (mainAt 22) := by
  apply reaches_mono state (mainAt 21) (mainAt 22)
    (AllocationDeclarationReady state (ofString "root") heap 32) _ 2 2 (by omega)
    _ (main_root_allocation_reaches state heap code atHeap capped budget)
  intro next allocation
  have saved := allocation
  obtain ⟨locals,memory,_,domain,_⟩ := saved
  have nextTable : HtrRequestsDecoded next record := by
    intro index inside
    obtain ⟨p,n,entry,small⟩ := table index inside
    exact ⟨p,n,entry.after_frame state next record index p n domain (congrFun memory _) (congrFun memory _),small⟩
  exact ⟨allocation,(by rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]),
    (by rw [locals]; simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "root" ≠ ofString "si" by decide] using atSi),
    header.after_frame domain (fun _ _ => congrFun memory _),nextTable,decoded.after_frame domain memory⟩

#print axioms main_hash_root_allocation_reaches
end InitECandidate.Runtime
