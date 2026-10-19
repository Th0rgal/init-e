import InitECandidate.Runtime.MainInitialHashCallBound
import InitECandidate.Runtime.HtrNewPayloadCallMemoryGuarded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- Main's initial hash retains the decoded input and metadata words between
the hash workspaces and its root output buffer. -/
theorem main_initial_hash_after_root_memory {F : Type} (state next post : PanSemStateFiniteExact 64 F)
    (heap si payload blobs blobCount parentRoot record array count input inputLength
      withdrawals withdrawalCount requests requestLength payloadBlobs blobLength watched : BitVec 64)
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
    (watchedLower : 2713715344 ≤ watched.toNat)
    (watchedBefore : watched.toNat < heap.toNat)
    (allocation : AllocationDeclarationReady state (ofString "root") heap 32 next)
    (budget : htrNewPayloadBodyCost + 1 ≤ next.clock)
    (run : evaluateHOLFiniteState next mainInitialHashCall = (none,post)) :
    post.memory watched = state.memory watched := by
  obtain ⟨locals,memory,installed,domain,globals,cap,covers,aligned⟩ := allocation
  have cover : heap.toNat + 32 ≤ (allocationEnd heap (32#64)).toNat := covers
  change (allocationEnd heap (32#64)).toNat ≤ 33806089496 at cap
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
  have layout : ListHashMemoryLayout next 2713714688 2713714880 2713715408 2713715312
      (allocationEnd heap (32#64)) heap watched :=
    ⟨⟨workspaceNext.atSha,workspaceNext.atAccel,workspaceNext.atZero,workspaceNext.atHeap,workspace.heapAligned,
      (by omega),Or.inl watchedBefore,aligned,cap,(by omega),(by decide),(by decide),(by decide),
      Or.inr (by change 2713714976 ≤ watched.toNat; omega),
      Or.inr (by change 2713714752 ≤ watched.toNat; omega),workspaceNext.code⟩,
      workspaceNext.atChunk,(by decide),(by decide),Or.inr (by change 2713715344 ≤ watched.toNat; exact watchedLower)⟩
  rw [← memory]
  unfold mainInitialHashCall at run
  apply htrNewPayload_call_normal_memory_guarded next post 2713714688 2713714880 2713715408 2713715312 record
    (allocationEnd heap (32#64)) si heap payload blobs blobCount parentRoot array count input inputLength input inputLength
    withdrawals withdrawalCount requests requestLength payloadBlobs blobLength watched workspaceNext layout tableNext
    (header.after_frame domain (fun _ _ => congrFun memory _)) (decoded.after_frame domain memory)
    _ args siRecord
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
  · exact run

#print axioms main_initial_hash_after_root_memory
end InitECandidate.Runtime
