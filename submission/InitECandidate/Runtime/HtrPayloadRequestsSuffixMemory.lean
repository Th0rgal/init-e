import InitECandidate.Runtime.HtrPayloadFinalSuffixMemory
import InitECandidate.Runtime.HtrPayloadRequestsSuffixBound
import InitECandidate.Runtime.ListHashMemoryLayout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrPayload_requests_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes chunk heap raw chunks out mark payload requests length watched : BitVec 64) (value : ValueHOL 64)
    (layout : ListHashMemoryLayout state sha accelerator zeroHashes chunk heap out watched)
    (atRaw : state.locals.lookup (ofString "raw") = some (.val (.word raw)))
    (atChunks : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (atPayload : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (entry : RlpSliceEntry state payload (4#64) requests length) (small : length.toNat ≤ 134217712)
    (chunksAligned : chunks.toNat % 8 = 0) (chunksFits : chunks.toNat + 608 ≤ 33806089496)
    (chunksBefore : watched.toNat < chunks.toNat)
    (budget : htrPayloadRequestsSuffixCost ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrPayloadAt 33) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  rw [source_htrPayload_requests] at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile _ (by decide) state v) run
  have args := htrPayload_requests_arguments state payload requests length chunks atPayload atChunks entry
  have natural : (chunks + (544#64)).toNat = chunks.toNat + 544 := word_add_toNat chunks 544 (by omega)
  have enough : htrPbytesBodyCost + 1 ≤ state.clock :=
    (Nat.le_add_right (htrPbytesBodyCost + 1) htrPayloadFinalSuffixCost).trans budget
  have frame := htrPbytes_call_normal_memory state middle htrPayloadRequestsArguments sha accelerator zeroHashes chunk requests length heap
    (chunks + (544#64)) watched args layout.atSha layout.atAccel layout.atChunk layout.chunkAligned layout.chunkFits layout.chunkOutside
    layout.atZero layout.atHeap (by rw [natural,Nat.add_mod,chunksAligned]) (by rw [natural]; omega)
    (Or.inl (by rw [natural]; omega)) small layout.heapAligned layout.heapFits layout.heapBefore layout.accelAligned layout.accelFits
    layout.shaFits layout.accelOutside layout.shaOutside layout.code enough normal
  have globals := htrPbytes_call_normal_globals state middle htrPayloadRequestsArguments requests length (chunks + (544#64)) heap
    args layout.atHeap layout.code normal
  have metadata := evaluateHOLFiniteState_metadata state
    (.call (some (none,none)) (ofString "htr_pbytes") htrPayloadRequestsArguments)
  have bounded := runBounded_htrPbytes_call state none htrPayloadRequestsArguments requests length (chunks + (544#64)) heap
    args small layout.atHeap layout.heapFits layout.code enough
  unfold RunBounded at bounded
  rw [normal] at metadata bounded
  have keep (key : MlS) : middle.locals.lookup key = state.locals.lookup key := by
    have kept := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "htr_pbytes") htrPayloadRequestsArguments)
      rfl state (by rw [normal]; exact Or.inl rfl)
    rw [normal] at kept
    exact kept
  have spent : state.clock ≤ middle.clock + (htrPbytesBodyCost + 1) := bounded.1
  have remaining : htrPayloadFinalSuffixCost ≤ middle.clock := by
    change (htrPbytesBodyCost + 1) + htrPayloadFinalSuffixCost ≤ state.clock at budget
    generalize htrPbytesBodyCost = pc at budget spent
    generalize htrPayloadFinalSuffixCost = cost at budget ⊢
    omega
  have suffix := htrPayload_final_suffix_returned_memory middle post sha accelerator zeroHashes heap raw chunks out mark watched value
    (layout.toHashMemoryLayout.transfer globals metadata.1) ((keep _).trans atRaw) ((keep _).trans atChunks)
    ((keep _).trans atOut) ((keep _).trans atMark) chunksAligned chunksFits chunksBefore remaining tail
  exact suffix.trans frame

#print axioms htrPayload_requests_suffix_returned_memory
end InitECandidate.Runtime
