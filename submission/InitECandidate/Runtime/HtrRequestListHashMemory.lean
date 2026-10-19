import InitECandidate.Runtime.ListHashMemoryLayout
import InitECandidate.Runtime.HtrRequestListSuffixBound
import InitECandidate.Runtime.HtrPlistChunksMemory
import InitECandidate.Runtime.HeapReleaseMemory
import InitECandidate.Runtime.HtabGrowFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrRequestList_hash_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes chunk roots count heap out mark watched : BitVec 64) (value : ValueHOL 64)
    (layout : ListHashMemoryLayout state sha accelerator zeroHashes chunk heap out watched)
    (atRoots : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (atCount : state.locals.lookup (ofString "n") = some (.val (.word count)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (small : count.toNat ≤ 134217712) (budget : htrPlistChunksCost + 2 ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrRequestListAt 4) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  let arguments : List (ExpHOL 64) := [.var .local (ofString "roots"),.var .local (ofString "n"),
    .var .local (ofString "n"),.var .local (ofString "out")]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word roots),.val (.word count),.val (.word count),.val (.word out)] := by
    simp [arguments,evalListHOLExact,evalHOLExact,atRoots,atCount,atOut]
  rw [source_htrRequestList_hash] at run
  obtain ⟨middle,normal,last⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return state (ofString "htr_plist_chunks") arguments v) run
  have frame := htrPlistChunks_call_normal_memory state middle arguments sha accelerator zeroHashes chunk roots count count heap out watched
    args layout.atSha layout.atAccel layout.atChunk layout.chunkAligned layout.chunkFits layout.chunkOutside layout.atZero layout.atHeap
    layout.outAligned layout.outFits layout.outOutside small layout.heapAligned layout.heapFits layout.heapBefore layout.accelAligned
    layout.accelFits layout.shaFits layout.accelOutside layout.shaOutside layout.code (by omega) normal
  have keepMark : middle.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    have kept := evaluate_avoidsLocal_flowing (ofString "mark") (.call (some (none,none)) (ofString "htr_plist_chunks") arguments)
      rfl state (by rw [normal]; exact Or.inl rfl)
    simpa only [normal] using kept.trans (by simpa only [normal] using atMark)
  have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "htr_plist_chunks") arguments)
  change evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_plist_chunks") arguments) = _ at normal
  rw [normal] at metadata
  obtain ⟨released,releaseRun,finishRun⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return middle (ofString "heap_release") [.var .local (ofString "mark")] v) last
  have releaseFrame := heapRelease_call_normal_memory middle released (.var .local (ofString "mark")) mark
    (metadata.1.trans layout.code) (by simp [evalListHOLExact,evalHOLExact,keepMark]) releaseRun
  obtain ⟨finishMemory,_,_,_⟩ := return_const_state released post 0 value finishRun
  rw [finishMemory,releaseFrame]
  exact frame

#print axioms htrRequestList_hash_returned_memory
end InitECandidate.Runtime
