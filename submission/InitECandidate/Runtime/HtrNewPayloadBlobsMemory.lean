import InitECandidate.Runtime.HtrNewPayloadBlobsBound
import InitECandidate.Runtime.HtrNewPayloadCopyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem htrNewPayload_blobs_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes chunk record heap si chunks out payload blobs count parentRoot mark watched : BitVec 64) (value : ValueHOL 64)
    (workspace : HtrRequestsWorkspace state sha accelerator zeroHashes chunk record heap)
    (layout : ListHashMemoryLayout state sha accelerator zeroHashes chunk heap out watched)
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (decoded : HtrRequestsDecoded state record)
    (header : HtrNewPayloadHeader state si payload blobs count parentRoot record)
    (atSi : state.locals.lookup (ofString "si") = some (.val (.word si)))
    (atChunks : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (chunksAligned : chunks.toNat % 8 = 0) (chunksHeap : chunks.toNat + 128 ≤ heap.toNat)
    (siRecord : si.toNat + 32 < record.toNat) (recordBefore : record.toNat + 72 < chunks.toNat)
    (shaSi : sha.toNat + 64 ≤ si.toNat) (accelSi : accelerator.toNat + 96 ≤ si.toNat)
    (chunkSi : chunk.toNat + 32 ≤ si.toNat)
    (before : watched.toNat < chunks.toNat)
    (budget : htrNewPayloadBlobsCost ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrNewPayloadAt 3) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have args := htrNewPayload_blobs_arguments state si chunks payload blobs count parentRoot record header atSi atChunks
  have enough : htrPlistChunksCost + 1 ≤ state.clock :=
    (Nat.le_add_right (htrPlistChunksCost + 1) htrNewPayloadCopyCost).trans budget
  have first := runBounded_htrPlistChunks_call state none htrNewPayloadBlobsArguments blobs count count (chunks + (32#64)) heap
    args header.countBound workspace.atHeap workspace.heapFits workspace.code enough
  have natural : (chunks + (32#64)).toNat = chunks.toNat + 32 := word_add_toNat chunks 32 (by have := workspace.heapFits; omega)
  have aligned : (chunks + (32#64)).toNat % 8 = 0 := by rw [natural,Nat.add_mod,chunksAligned]
  rw [source_htrNewPayload_blobs] at run
  obtain ⟨next,normal,last⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return state (ofString "htr_plist_chunks") htrNewPayloadBlobsArguments v) run
  have spent := first.1
  rw [normal] at spent
  change state.clock ≤ next.clock + (htrPlistChunksCost + 1) at spent
  have remaining : htrNewPayloadCopyCost ≤ next.clock := by
    change (htrPlistChunksCost + 1) + htrNewPayloadCopyCost ≤ state.clock at budget
    omega
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
  have watchedFrame := htrPlistChunks_call_normal_memory state next htrNewPayloadBlobsArguments sha accelerator zeroHashes chunk blobs count count heap
    (chunks + (32#64)) watched args layout.atSha layout.atAccel layout.atChunk layout.chunkAligned layout.chunkFits
    layout.chunkOutside layout.atZero layout.atHeap aligned (by rw [natural]; have := workspace.heapFits; omega)
    (Or.inl (by rw [natural]; omega)) header.countBound layout.heapAligned layout.heapFits (by omega) layout.accelAligned
    layout.accelFits layout.shaFits layout.accelOutside layout.shaOutside layout.code enough normal
  have tailFrame := htrNewPayload_copy_returned_memory next post sha accelerator zeroHashes chunk record heap si chunks out parentRoot mark watched value
    (workspace.transfer globals metadata.1) (layout.transfer globals metadata.1) ((keep _).trans atMark) decodedKept
    ((keep _).trans atSi) ((keep _).trans atChunks) ((keep _).trans atOut)
    headerKept.requestsDomain headerKept.requestsCell headerKept.parentDomain headerKept.parentCell chunksAligned
    (by have := workspace.heapFits; omega) (by omega) recordBefore before remaining last
  exact tailFrame.trans watchedFrame

#print axioms htrNewPayload_blobs_returned_memory
end InitECandidate.Runtime
