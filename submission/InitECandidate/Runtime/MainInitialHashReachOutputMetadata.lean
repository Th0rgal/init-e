import InitECandidate.Runtime.MainInitialHashMetadata
import InitECandidate.Runtime.RunBoundedSeqReach
import InitECandidate.Runtime.NormalRelLocalCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- Main's root allocation and installed initial hash reach the actual VM
validation continuation within a finite uniform cost or abort earlier. -/
theorem main_root_initial_hash_reaches_output_metadata {F : Type} (state : PanSemStateFiniteExact 64 F)
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
      (fun post => HtrNewPayloadHeader post si payload blobs blobCount parentRoot record ∧
        HtrRequestsDecoded post record ∧
        HtrPayloadDecoded post payload array count input inputLength input inputLength
          withdrawals withdrawalCount requests requestLength payloadBlobs blobLength ∧
        post.locals.lookup (ofString "si") = some (.val (.word si)) ∧
        post.locals.lookup (ofString "root") = some (.val (.word heap)) ∧
        post.globals = (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word (allocationEnd heap 32))) state).globals ∧
        post.memaddrs = state.memaddrs ∧ post.code = originalRuntimeCode ∧
        (∀ watched : BitVec 64, 2713715344 ≤ watched.toNat → watched.toNat < heap.toNat →
          post.memory watched = state.memory watched) ∧
        post.locals.lookup (ofString "out")=state.locals.lookup (ofString "out"))
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
    have callBudget : htrNewPayloadBodyCost + 1 ≤ next.clock := by omega
    obtain ⟨headerKept,tableKept,payloadKept,siKept,globalsKept,domainKept⟩ :=
      main_initial_hash_after_root_metadata state next post heap si payload blobs blobCount parentRoot record array count
        input inputLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength workspace atSi header table decoded
        siLower payloadAfter siRecord payloadExtent arrayExtent origin allocation callBudget run
    have frame (watched : BitVec 64) (lo : 2713715344 ≤ watched.toNat) (hi : watched.toNat < heap.toNat) :
        post.memory watched = state.memory watched :=
      main_initial_hash_after_root_memory state next post heap si payload blobs blobCount parentRoot record array count
        input inputLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength watched workspace atSi header table decoded
        siLower payloadAfter siRecord payloadExtent arrayExtent origin lo hi allocation callBudget run
    obtain ⟨rootLocals,rootMemory,rootCode,rootDomain,rootGlobals,rootCap,rootCovers,rootAligned⟩ := allocation
    have rootKept : post.locals.lookup (ofString "root") = some (.val (.word heap)) := by
      have kept := evaluate_avoidsLocal_flowing (ofString "root") mainInitialHashCall rfl next (by rw [run]; exact Or.inl rfl)
      rw [run] at kept
      rw [kept,rootLocals]
      simp (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE]
    have metadata := evaluateHOLFiniteState_metadata next mainInitialHashCall
    rw [run] at metadata
    have outKept : post.locals.lookup (ofString "out")=state.locals.lookup (ofString "out") := by
      have kept := evaluate_avoidsLocal_flowing (ofString "out") mainInitialHashCall rfl next (by rw [run]; exact Or.inl rfl)
      rw [run] at kept
      rw [kept,rootLocals]
      simp (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE]
    exact ⟨headerKept,tableKept,payloadKept,siKept,rootKept,globalsKept.trans rootGlobals,domainKept,
      metadata.1.trans (rootCode.trans workspace.code),frame,outKept⟩

#print axioms main_root_initial_hash_reaches_output_metadata
end InitECandidate.Runtime
