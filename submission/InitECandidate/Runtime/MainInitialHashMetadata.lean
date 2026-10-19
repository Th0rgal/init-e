import InitECandidate.Runtime.MainInitialHashMemory
import InitECandidate.Runtime.HtrNewPayloadGlobals
import InitECandidate.Runtime.HtrPayloadDecodedIntervalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- The actual initial hash carries the decoded header, requests, and transaction
slices into VM validation, with the root allocation's global map intact. -/
theorem main_initial_hash_after_root_metadata {F : Type} (state next post : PanSemStateFiniteExact 64 F)
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
    (budget : htrNewPayloadBodyCost + 1 ≤ next.clock)
    (run : evaluateHOLFiniteState next mainInitialHashCall = (none,post)) :
    HtrNewPayloadHeader post si payload blobs blobCount parentRoot record ∧
      HtrRequestsDecoded post record ∧
      HtrPayloadDecoded post payload array count input inputLength input inputLength
        withdrawals withdrawalCount requests requestLength payloadBlobs blobLength ∧
      post.locals.lookup (ofString "si") = some (.val (.word si)) ∧
      post.globals = next.globals ∧ post.memaddrs = state.memaddrs := by
  have frame (watched : BitVec 64) (lo : 2713715344 ≤ watched.toNat) (hi : watched.toNat < heap.toNat) :
      post.memory watched = state.memory watched :=
    main_initial_hash_after_root_memory state next post heap si payload blobs blobCount parentRoot record array count input inputLength
      withdrawals withdrawalCount requests requestLength payloadBlobs blobLength watched workspace atSi header table decoded
      siLower payloadAfter siRecord payloadExtent arrayExtent origin lo hi allocation budget run
  obtain ⟨locals,memory,installed,domain,globals,cap,covers,aligned⟩ := allocation
  have metadata := evaluateHOLFiniteState_metadata next mainInitialHashCall
  rw [run] at metadata
  have addresses : post.memaddrs = state.memaddrs := metadata.2.1.trans domain
  have headerKept := header.after_frame addresses (by
    intro offset inside
    have natural : (si + offset).toNat = si.toNat + offset.toNat := BitVec.toNat_add_of_lt
      (by have := workspace.recordHeap; have := workspace.heapFits; omega)
    exact frame _ (by rw [natural]; omega) (by rw [natural]; have := workspace.recordHeap; omega))
  have tableKept : HtrRequestsDecoded post record := by
    intro index inside
    obtain ⟨p,n,entry,small⟩ := table index inside
    exact ⟨p,n,entry.after_record_frame state post record index p n inside
      (by have := workspace.recordHeap; have := workspace.heapFits; omega) addresses
      (fun w lo hi => frame w (by omega) (by have := workspace.recordHeap; omega)),small⟩
  have payloadKept := decoded.after_interval_frame
    (by have := workspace.heapFits; omega) (by have := workspace.heapFits; omega) addresses
    (fun w lo hi => frame w (by omega) (by omega))
    (by
      intro w lo hi
      have beyond : payload.toNat + 136 ≤ array.toNat := by
        rcases origin with empty | beyond
        · subst count
          change w.toNat < array.toNat + 0 * 16 at hi
          omega
        · exact beyond
      exact frame w (by omega) (by omega))
  have nextSi : next.locals.lookup (ofString "si") = some (.val (.word si)) := by
    rw [locals]
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "root" ≠ ofString "si" by decide] using atSi
  have nextRoot : next.locals.lookup (ofString "root") = some (.val (.word heap)) := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have siKept : post.locals.lookup (ofString "si") = some (.val (.word si)) := by
    have kept := evaluate_avoidsLocal_flowing (ofString "si") mainInitialHashCall rfl next (by rw [run]; exact Or.inl rfl)
    rw [run] at kept
    exact kept.trans nextSi
  have args : evalListHOLFinite next (h := fun a => Classical.propDecidable (next.memaddrs a))
      [.var .local (ofString "si"),.var .local (ofString "root")] = some [.val (.word si),.val (.word heap)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,nextSi,nextRoot]
  have atHeap : next.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd heap 32))) := by
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have callRun := run
  unfold mainInitialHashCall at callRun
  have sameGlobals := htrNewPayload_call_normal_globals next post
    [.var .local (ofString "si"),.var .local (ofString "root")] si heap (allocationEnd heap 32)
    args atHeap (installed.trans workspace.code) callRun
  exact ⟨headerKept,tableKept,payloadKept,siKept,sameGlobals,addresses⟩

#print axioms main_initial_hash_after_root_metadata
end InitECandidate.Runtime
