import InitECandidate.Runtime.MainHashRootAllocation
import InitECandidate.Runtime.HtrNewPayloadCallGuarded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def mainInitialHashCall : ProgHOL 64 :=
  .call (some (none,none)) (ofString "htr_new_payload_request")
    [.var .local (ofString "si"),.var .local (ofString "root")]

theorem source_main_initial_hash_call : mainAt 22 = .seq mainInitialHashCall (mainAt 23) := by
  simp only [mainAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The actual root allocation establishes the installed initial hash call's
runtime premises. In particular, an empty transaction array needs no separation. -/
theorem main_initial_hash_after_root_bounded {F : Type} (state next : PanSemStateFiniteExact 64 F)
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
    (allocation : AllocationDeclarationReady state (ofString "root") heap 32 next)
    (budget : htrNewPayloadBodyCost + 1 ≤ next.clock) :
    RunBounded next mainInitialHashCall (htrNewPayloadBodyCost + 1) := by
  obtain ⟨locals,memory,installed,domain,globals,cap,covers,aligned⟩ := allocation
  have cover : heap.toNat + 32 ≤ (allocationEnd heap (32#64)).toNat := covers
  have nonHeap (key : MlS) (different : key ≠ ofString "heap_ptr") :
      next.globals.lookup key = state.globals.lookup key := by
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have workspaceNext : HtrRequestsWorkspace next 2713714688 2713714880 2713715408 2713715312 record
      (allocationEnd heap (32#64)) :=
    ⟨(nonHeap _ (by decide)).trans workspace.atSha,(nonHeap _ (by decide)).trans workspace.atAccel,
      (nonHeap _ (by decide)).trans workspace.atZero,(nonHeap _ (by decide)).trans workspace.atChunk,
      (by rw [globals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]),aligned,cap,
      (by have := workspace.recordHeap; omega),workspace.accelAligned,workspace.chunkAligned,
      workspace.shaRecord,workspace.accelRecord,workspace.chunkRecord,installed.trans workspace.code⟩
  have nextSi : next.locals.lookup (ofString "si") = some (.val (.word si)) := by
    rw [locals]
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "root" ≠ ofString "si" by decide] using atSi
  have nextRoot : next.locals.lookup (ofString "root") = some (.val (.word heap)) := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have args : evalListHOLFinite next (h := fun a => Classical.propDecidable (next.memaddrs a))
      [.var .local (ofString "si"),.var .local (ofString "root")] =
      some [.val (.word si),.val (.word heap)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,nextSi,nextRoot]
  have tableNext : HtrRequestsDecoded next record := by
    intro index inside
    obtain ⟨p,n,entry,small⟩ := table index inside
    exact ⟨p,n,entry.after_frame state next record index p n domain (congrFun memory _) (congrFun memory _),small⟩
  have nonempty (nz : count ≠ 0) : payload.toNat + 136 ≤ array.toNat := by
    rcases origin with empty | beyond
    · exact False.elim (nz empty)
    · exact beyond
  unfold mainInitialHashCall
  apply runBounded_htrNewPayload_call_guarded next 2713714688 2713714880 2713715408 2713715312 record
    (allocationEnd heap (32#64)) si heap payload blobs blobCount parentRoot array count input inputLength input inputLength
    withdrawals withdrawalCount requests requestLength payloadBlobs blobLength workspaceNext tableNext
    (header.after_frame domain (fun _ _ => congrFun memory _)) (decoded.after_frame domain memory)
    none _ args siRecord
  · have := workspace.recordHeap; omega
  · change 2713714752 ≤ si.toNat; omega
  · change 2713714976 ≤ si.toNat; omega
  · change 2713715344 ≤ si.toNat; exact siLower
  · omega
  · intro nz; have := nonempty nz; change 2713715344 ≤ array.toNat; omega
  · intro nz; have := nonempty nz; change 2713714976 ≤ array.toNat; omega
  · intro nz; have := nonempty nz; change 2713714752 ≤ array.toNat; omega
  · omega
  · change 2713715344 ≤ payload.toNat; omega
  · change 2713714976 ≤ payload.toNat; omega
  · change 2713714752 ≤ payload.toNat; omega
  · exact budget

#print axioms source_main_initial_hash_call
#print axioms main_initial_hash_after_root_bounded
end InitECandidate.Runtime
