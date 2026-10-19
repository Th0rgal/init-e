import InitECandidate.Runtime.HtrNewPayloadCopyBound
import InitECandidate.Runtime.HtrNewPayloadHeader
import InitECandidate.Runtime.HtrPlistChunksMemory
import InitECandidate.Runtime.HtrPlistChunksGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def htrNewPayloadBlobsCost : Nat := (htrPlistChunksCost + 1) + htrNewPayloadCopyCost

/-- The actual blobs-list hash preserves the header and request-table entries,
then the parent-root copy and requests/final-Merkle suffix are bounded. -/
theorem runBounded_htrNewPayload_blobs_suffix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes chunk record heap si chunks out payload blobs count parentRoot : BitVec 64)
    (workspace : HtrRequestsWorkspace state sha accelerator zeroHashes chunk record heap)
    (decoded : HtrRequestsDecoded state record)
    (header : HtrNewPayloadHeader state si payload blobs count parentRoot record)
    (atSi : state.locals.lookup (ofString "si") = some (.val (.word si)))
    (atChunks : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (chunksAligned : chunks.toNat % 8 = 0) (chunksHeap : chunks.toNat + 128 ≤ heap.toNat)
    (siRecord : si.toNat + 32 < record.toNat) (recordBefore : record.toNat + 72 < chunks.toNat)
    (shaSi : sha.toNat + 64 ≤ si.toNat) (accelSi : accelerator.toNat + 96 ≤ si.toNat)
    (chunkSi : chunk.toNat + 32 ≤ si.toNat)
    (budget : htrNewPayloadBlobsCost ≤ state.clock) :
    RunBounded state (htrNewPayloadAt 3) htrNewPayloadBlobsCost := by
  have args := htrNewPayload_blobs_arguments state si chunks payload blobs count parentRoot record header atSi atChunks
  have enough : htrPlistChunksCost + 1 ≤ state.clock :=
    (Nat.le_add_right (htrPlistChunksCost + 1) htrNewPayloadCopyCost).trans budget
  have first := runBounded_htrPlistChunks_call state none htrNewPayloadBlobsArguments blobs count count (chunks + (32#64)) heap
    args header.countBound workspace.atHeap workspace.heapFits workspace.code enough
  have natural : (chunks + (32#64)).toNat = chunks.toNat + 32 := word_add_toNat chunks 32 (by have := workspace.heapFits; omega)
  have aligned : (chunks + (32#64)).toNat % 8 = 0 := by rw [natural,Nat.add_mod,chunksAligned]
  rw [source_htrNewPayload_blobs]
  exact RunBounded.seq first budget (by
    intro next normal nextCode remaining
    have globals := htrPlistChunks_call_normal_globals state next htrNewPayloadBlobsArguments blobs count count (chunks + (32#64)) heap
      args workspace.atHeap workspace.code normal
    have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "htr_plist_chunks") htrNewPayloadBlobsArguments)
    rw [normal] at metadata
    have frame (watched : BitVec 64) (lo : si.toNat ≤ watched.toNat) (hi : watched.toNat < chunks.toNat) :
        next.memory watched = state.memory watched := by
      exact htrPlistChunks_call_normal_memory state next htrNewPayloadBlobsArguments sha accelerator zeroHashes chunk blobs count count heap
        (chunks + (32#64)) watched args workspace.atSha workspace.atAccel workspace.atChunk workspace.chunkAligned
        (by have := workspace.heapFits; omega) (Or.inr (by omega)) workspace.atZero workspace.atHeap aligned
        (by rw [natural]; have := workspace.heapFits; omega) (Or.inl (by rw [natural]; omega)) header.countBound
        workspace.heapAligned workspace.heapFits (by omega) workspace.accelAligned (by have := workspace.heapFits; omega)
        (by have := workspace.heapFits; omega) (Or.inr (by omega)) (Or.inr (by omega)) workspace.code enough normal
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
      have kept := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "htr_plist_chunks") htrNewPayloadBlobsArguments)
        rfl state (by rw [normal]; exact Or.inl rfl)
      rw [normal] at kept
      exact kept
    exact runBounded_htrNewPayload_copy_suffix next sha accelerator zeroHashes chunk record heap si chunks out parentRoot
      (workspace.transfer globals nextCode) decodedKept ((keep _).trans atSi) ((keep _).trans atChunks) ((keep _).trans atOut)
      headerKept.requestsDomain headerKept.requestsCell headerKept.parentDomain headerKept.parentCell chunksAligned
      (by have := workspace.heapFits; omega) (by omega) recordBefore remaining)

#print axioms runBounded_htrNewPayload_blobs_suffix
end InitECandidate.Runtime
