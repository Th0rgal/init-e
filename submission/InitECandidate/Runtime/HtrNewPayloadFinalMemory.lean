import InitECandidate.Runtime.HtrNewPayloadFinalBound
import InitECandidate.Runtime.MerkleizeMemory
import InitECandidate.Runtime.HtrRequestsMemory
import InitECandidate.Runtime.HeapReleaseMemory
import InitECandidate.Runtime.HtabGrowFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem htrNewPayload_final_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes chunks out heap mark watched : BitVec 64) (value : ValueHOL 64)
    (layout : HashMemoryLayout state sha accelerator zeroHashes heap out watched)
    (atChunks : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (budget : htrNewPayloadFinalCost ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrNewPayloadAt 6) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) htrNewPayloadMerkleArguments =
      some [.val (.word chunks),.val (.word (4#64)),.val (.word (4#64)),.val (.word out)] := by
    simp [htrNewPayloadMerkleArguments,evalListHOLExact,evalHOLExact,atChunks,atOut]
  rw [source_htrNewPayload_merkle] at run
  obtain ⟨middle,normal,last⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return state (ofString "merkleize") htrNewPayloadMerkleArguments v) run
  have frame := merkleize_call_normal_memory state middle htrNewPayloadMerkleArguments sha accelerator heap zeroHashes 4 out 4 chunks watched
    args layout.atSha layout.atAccel layout.atZero layout.atHeap layout.heapFits (by decide) layout.outAligned layout.outFits
    layout.outOutside layout.heapAligned layout.heapBefore layout.accelAligned layout.accelFits layout.shaFits layout.accelOutside
    layout.shaOutside layout.code (by change (merkleBodyCost + 1) + 1 ≤ state.clock at budget; omega) normal
  have keepMark : middle.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    have kept := evaluate_avoidsLocal_flowing (ofString "mark") (.call (some (none,none)) (ofString "merkleize") htrNewPayloadMerkleArguments)
      rfl state (by rw [normal]; exact Or.inl rfl)
    rw [normal] at kept
    exact kept.trans atMark
  have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "merkleize") htrNewPayloadMerkleArguments)
  rw [normal] at metadata
  rw [source_htrNewPayload_finish] at last
  obtain ⟨released,releaseRun,finishRun⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return middle (ofString "heap_release") [.var .local (ofString "mark")] v) last
  have releaseFrame := heapRelease_call_normal_memory middle released (.var .local (ofString "mark")) mark
    (metadata.1.trans layout.code) (by simp [evalListHOLExact,evalHOLExact,keepMark]) releaseRun
  obtain ⟨finishMemory,_,_,_⟩ := return_const_state released post 0 value finishRun
  rw [finishMemory,releaseFrame]
  exact frame

theorem htrNewPayload_requests_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes chunk record heap si chunks out mark watched : BitVec 64) (value : ValueHOL 64)
    (workspace : HtrRequestsWorkspace state sha accelerator zeroHashes chunk record heap)
    (decoded : HtrRequestsDecoded state record)
    (layout : ListHashMemoryLayout state sha accelerator zeroHashes chunk heap out watched)
    (atSi : state.locals.lookup (ofString "si") = some (.val (.word si)))
    (atChunks : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (domain : state.memaddrs (si + (32#64))) (cell : state.memory (si + (32#64)) = .word record)
    (chunksAligned : chunks.toNat % 8 = 0) (chunksFits : chunks.toNat + 128 ≤ 33806089496)
    (before : watched.toNat < chunks.toNat)
    (budget : htrNewPayloadRequestsCost ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrNewPayloadAt 5) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have args := htrNewPayload_requests_arguments state si chunks record atSi atChunks domain cell
  have enough : htrRequestsBodyCost + 1 ≤ state.clock := (Nat.le_add_right _ _).trans budget
  have natural : (chunks + (96#64)).toNat = chunks.toNat + 96 := word_add_toNat chunks 96 (by omega)
  have outputAligned : (chunks + (96#64)).toNat % 8 = 0 := by rw [natural,Nat.add_mod,chunksAligned]
  have requestLayout : ListHashMemoryLayout state sha accelerator zeroHashes chunk heap (chunks + (96#64)) watched :=
    ⟨⟨layout.atSha,layout.atAccel,layout.atZero,layout.atHeap,outputAligned,(by rw [natural]; omega),
      Or.inl (by rw [natural]; omega),layout.heapAligned,layout.heapFits,layout.heapBefore,
      layout.accelAligned,layout.accelFits,layout.shaFits,layout.accelOutside,layout.shaOutside,layout.code⟩,
      layout.atChunk,layout.chunkAligned,layout.chunkFits,layout.chunkOutside⟩
  rw [source_htrNewPayload_requests] at run
  obtain ⟨middle,normal,last⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return state (ofString "htr_requests") htrNewPayloadRequestsArguments v) run
  have frame := htrRequests_call_normal_memory state middle htrNewPayloadRequestsArguments sha accelerator zeroHashes chunk record heap
    (chunks + (96#64)) watched workspace decoded requestLayout args enough normal
  have globals := htrRequests_call_normal_globals state middle htrNewPayloadRequestsArguments record (chunks + (96#64)) heap
    args workspace.atHeap workspace.code normal
  have keep (key : MlS) : middle.locals.lookup key = state.locals.lookup key := by
    have kept := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "htr_requests") htrNewPayloadRequestsArguments)
      rfl state (by rw [normal]; exact Or.inl rfl)
    rw [normal] at kept
    exact kept
  have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "htr_requests") htrNewPayloadRequestsArguments)
  rw [normal] at metadata
  have spent := (runBounded_htrRequests_call state none htrNewPayloadRequestsArguments sha accelerator zeroHashes chunk record heap
    (chunks + (96#64)) workspace decoded args enough).1
  rw [normal] at spent
  change state.clock ≤ middle.clock + (htrRequestsBodyCost + 1) at spent
  have remaining : htrNewPayloadFinalCost ≤ middle.clock := by
    change (htrRequestsBodyCost + 1) + htrNewPayloadFinalCost ≤ state.clock at budget
    omega
  have tail := htrNewPayload_final_returned_memory middle post sha accelerator zeroHashes chunks out heap mark watched value
    (layout.toHashMemoryLayout.transfer globals metadata.1) ((keep _).trans atChunks) ((keep _).trans atOut)
    ((keep _).trans atMark) remaining last
  exact tail.trans frame

#print axioms htrNewPayload_final_returned_memory
#print axioms htrNewPayload_requests_returned_memory
end InitECandidate.Runtime
