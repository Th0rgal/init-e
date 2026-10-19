import InitECandidate.Runtime.HtrNewPayloadPayloadBound
import InitECandidate.Runtime.HtrPayloadCallGuarded
import InitECandidate.Runtime.HtrPayloadCallMemoryGuarded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem runBounded_htrNewPayload_payload_suffix_guarded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes chunk record heap si chunks out payload blobs blobCount parentRoot
      array count input inputLength raw rawLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength : BitVec 64)
    (workspace : HtrRequestsWorkspace state sha accelerator zeroHashes chunk record heap)
    (decoded : HtrRequestsDecoded state record)
    (header : HtrNewPayloadHeader state si payload blobs blobCount parentRoot record)
    (payloadDecoded : HtrPayloadDecoded state payload array count input inputLength raw rawLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength)
    (atSi : state.locals.lookup (ofString "si") = some (.val (.word si)))
    (atChunks : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (chunksAligned : chunks.toNat % 8 = 0) (chunksHeap : chunks.toNat + 128 ≤ heap.toNat)
    (siRecord : si.toNat + 32 < record.toNat) (recordBefore : record.toNat + 72 < chunks.toNat)
    (shaSi : sha.toNat + 64 ≤ si.toNat) (accelSi : accelerator.toNat + 96 ≤ si.toNat)
    (chunkSi : chunk.toNat + 32 ≤ si.toNat)
    (arrayHeap : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (chunkArray : count ≠ 0 → chunk.toNat + 32 ≤ array.toNat)
    (accelArray : count ≠ 0 → accelerator.toNat + 96 ≤ array.toNat) (shaArray : count ≠ 0 → sha.toNat + 64 ≤ array.toNat)
    (payloadHeap : payload.toNat + 72 < heap.toNat)
    (chunkPayload : chunk.toNat + 32 ≤ payload.toNat)
    (accelPayload : accelerator.toNat + 96 ≤ payload.toNat) (shaPayload : sha.toNat + 64 ≤ payload.toNat)
    (budget : htrNewPayloadPayloadCost ≤ state.clock) :
    RunBounded state (htrNewPayloadAt 2) htrNewPayloadPayloadCost := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) htrNewPayloadPayloadArguments =
      some [.val (.word payload),.val (.word chunks)] := by
    have domain := header.payloadDomain
    have cell := header.payloadCell
    simp only [BitVec.add_zero] at domain cell
    simp [htrNewPayloadPayloadArguments,htrNewPayloadRead,evalListHOLExact,evalHOLExact,
      atSi,atChunks,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,domain,cell]
  have enough : htrPayloadUniformCost + 1 ≤ state.clock :=
    (Nat.le_add_right (htrPayloadUniformCost + 1) htrNewPayloadBlobsCost).trans budget
  have first := runBounded_htrPayload_call_guarded sha accelerator zeroHashes chunk array heap input inputLength count payload
    withdrawals withdrawalCount requests requestLength raw rawLength chunks payloadBlobs blobLength
    payloadDecoded.small payloadDecoded.countBound arrayHeap workspace.chunkAligned chunkArray workspace.heapAligned workspace.heapFits
    workspace.accelAligned accelArray shaArray payloadHeap chunkPayload accelPayload shaPayload state none htrNewPayloadPayloadArguments args
    workspace.code workspace.atSha workspace.atAccel workspace.atZero workspace.atChunk workspace.atHeap
    payloadDecoded.transactions payloadDecoded.slices payloadDecoded.rawEntry payloadDecoded.withdrawalEntry payloadDecoded.withdrawalBound
    payloadDecoded.requestEntry payloadDecoded.requestBound payloadDecoded.blobEntry payloadDecoded.blobBound enough
  rw [source_htrNewPayload_payload]
  exact RunBounded.seq first budget (by
    intro next normal nextCode remaining
    have globals := htrPayload_call_normal_globals state next htrNewPayloadPayloadArguments payload chunks heap
      args workspace.atHeap workspace.code normal
    have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "htr_payload") htrNewPayloadPayloadArguments)
    rw [normal] at metadata
    have frame (watched : BitVec 64) (lo : si.toNat ≤ watched.toNat) (hi : watched.toNat < chunks.toNat) :
        next.memory watched = state.memory watched := by
      have layout : ListHashMemoryLayout state sha accelerator zeroHashes chunk heap chunks watched :=
        ⟨⟨workspace.atSha,workspace.atAccel,workspace.atZero,workspace.atHeap,chunksAligned,
          (by have := workspace.heapFits; omega),Or.inl hi,workspace.heapAligned,workspace.heapFits,
          (by omega),workspace.accelAligned,(by have := workspace.heapFits; omega),
          (by have := workspace.heapFits; omega),Or.inr (by omega),Or.inr (by omega),workspace.code⟩,
          workspace.atChunk,workspace.chunkAligned,(by have := workspace.heapFits; omega),Or.inr (by omega)⟩
      exact htrPayload_call_normal_memory_guarded sha accelerator zeroHashes chunk array heap input inputLength count payload
        withdrawals withdrawalCount requests requestLength raw rawLength chunks payloadBlobs blobLength watched
        payloadDecoded.small payloadDecoded.countBound arrayHeap workspace.chunkAligned chunkArray workspace.heapAligned workspace.heapFits
        workspace.accelAligned accelArray shaArray payloadHeap chunkPayload accelPayload shaPayload state next layout htrNewPayloadPayloadArguments args
        workspace.code workspace.atSha workspace.atAccel workspace.atZero workspace.atChunk workspace.atHeap
        payloadDecoded.transactions payloadDecoded.slices payloadDecoded.rawEntry payloadDecoded.withdrawalEntry payloadDecoded.withdrawalBound
        payloadDecoded.requestEntry payloadDecoded.requestBound payloadDecoded.blobEntry payloadDecoded.blobBound enough normal
    have headerKept := header.after_frame metadata.2.1 (by
      intro offset inside
      have address : (si + offset).toNat = si.toNat + offset.toNat := BitVec.toNat_add_of_lt (by have := workspace.heapFits; omega)
      exact frame _ (by rw [address]; omega) (by rw [address]; omega))
    have decodedKept : HtrRequestsDecoded next record := by
      intro index inside
      obtain ⟨pointer,n,entry,small⟩ := decoded index inside
      refine ⟨pointer,n,?_,small⟩
      apply entry.after_record_frame state next record index pointer n inside (by have := workspace.heapFits; omega) metadata.2.1
      intro watched lo hi
      exact frame watched (by omega) (by omega)
    have keep (key : MlS) : next.locals.lookup key = state.locals.lookup key := by
      have kept := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "htr_payload") htrNewPayloadPayloadArguments)
        rfl state (by rw [normal]; exact Or.inl rfl)
      rw [normal] at kept
      exact kept
    exact runBounded_htrNewPayload_blobs_suffix next sha accelerator zeroHashes chunk record heap si chunks out payload blobs blobCount parentRoot
      (workspace.transfer globals nextCode) decodedKept headerKept ((keep _).trans atSi) ((keep _).trans atChunks) ((keep _).trans atOut)
      chunksAligned chunksHeap siRecord recordBefore shaSi accelSi chunkSi remaining)

#print axioms runBounded_htrNewPayload_payload_suffix_guarded
end InitECandidate.Runtime
