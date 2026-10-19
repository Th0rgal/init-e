import InitECandidate.Runtime.HtrNewPayloadBlobsBound
import InitECandidate.Runtime.HtrPayloadCallBound
import InitECandidate.Runtime.HtrPayloadCallMemory
import InitECandidate.Runtime.HtrPayloadGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- Decoded payload fields needed by the original payload hash. All entries
refer to the actual caller memory, including each transaction input slice. -/
structure HtrPayloadDecoded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (payload array count input inputLength raw rawLength withdrawals withdrawalCount requests requestLength blobs blobLength : BitVec 64) : Prop where
  small : inputLength.toNat ≤ 134217712
  countBound : count.toNat ≤ 134217712
  transactions : RlpSliceEntry state payload (2#64) array count
  slices : RlpSliceInputPrefix state array input inputLength count.toNat
  rawEntry : RlpSliceEntry state payload (0#64) raw rawLength
  withdrawalEntry : RlpSliceEntry state payload (3#64) withdrawals withdrawalCount
  withdrawalBound : withdrawalCount.toNat ≤ 134217712
  requestEntry : RlpSliceEntry state payload (4#64) requests requestLength
  requestBound : requestLength.toNat ≤ 134217712
  blobEntry : RlpSliceEntry state payload (1#64) blobs blobLength
  blobBound : blobLength.toNat ≤ 134217712

def htrNewPayloadPayloadCost : Nat := (htrPayloadUniformCost + 1) + htrNewPayloadBlobsCost

/-- The payload hash at its actual call site, followed by the complete blobs,
parent-root, requests and Merkle suffix. Successful payload hashing frames the
outer header and the decoded requests table; exceptional outcomes are bounded
by the payload call contract itself. -/
theorem runBounded_htrNewPayload_payload_suffix {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (chunkArray : chunk.toNat + 32 ≤ array.toNat)
    (accelArray : accelerator.toNat + 96 ≤ array.toNat) (shaArray : sha.toNat + 64 ≤ array.toNat)
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
  have first := runBounded_htrPayload_call sha accelerator zeroHashes chunk array heap input inputLength count payload
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
      exact htrPayload_call_normal_memory sha accelerator zeroHashes chunk array heap input inputLength count payload
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

#print axioms runBounded_htrNewPayload_payload_suffix
end InitECandidate.Runtime
