import InitECandidate.Runtime.BaselineLoopCode
import InitECandidate.Runtime.BaselineNativeOutcomes
import InitECandidate.Runtime.SelectedStackFields
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Compiler.Backend

theorem entryFrontendState_heap_words {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) :
    ∃ base capacity : BitVec 64,
      (entryFrontendState entry).store.lookup .currHeap = some (.word base) ∧
      (entryFrontendState entry).store.lookup .heapLength = some (.word capacity) := by
  obtain ⟨base,capacity,heap,length⟩ := StackRemove.selected_heap_words _ _ _ _ _ _ _ _ _ _ _ entry.selection
  refine ⟨base,capacity,?_,?_⟩
  · change (entry.source.store.eraseEq .handler).lookup .currHeap = _
    simpa [HolFiniteMapExact.lookup_eraseEq,FDOMSUB_HOL] using heap
  · change (entry.source.store.eraseEq .handler).lookup .heapLength = _
    simpa [HolFiniteMapExact.lookup_eraseEq,FDOMSUB_HOL] using length

/-- Exact Loop carrier matching all observable fields of frontend Word entry. -/
noncomputable def entryLoopState {input : Guest.InputBlob} (entry : BaselineRuntimeEntry input)
    (base capacity : BitVec 64) : LoopSemStateFiniteExact 64 Guest.HostMemory where
  locals := .ln
  globals := HolFiniteMapExact.empty
  memory := (entryFrontendState entry).memory
  mdomain := (entryFrontendState entry).mdomain
  shMdomain := (entryFrontendState entry).shMdomain
  clock := (entryFrontendState entry).clock
  code := sptFromAList FrontendStages.pass4
  be := (entryFrontendState entry).be
  ffi := (entryFrontendState entry).ffi
  baseAddr := base
  topAddr := base + 2 * capacity

theorem entryLoopState_related {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) (base capacity : BitVec 64)
    (heap : (entryFrontendState entry).store.lookup .currHeap = some (.word base))
    (length : (entryFrontendState entry).store.lookup .heapLength = some (.word capacity)) :
    loopToWordStateRelHOLExact (entryLoopState entry base capacity) (entryFrontendState entry) := by
  refine ⟨capacity,rfl,rfl,rfl,rfl,rfl,rfl,heap,length,rfl,?_,baseline_loop_word_codeRel⟩
  intro name value lookup
  change HolFiniteMapExact.empty.lookup name = some value at lookup
  simp [HolFiniteMapExact.empty] at lookup

/-- Actual initialization supplies a related Loop state without extra heap or
code assumptions. Earlier frontend passes must still relate their state to it. -/
theorem entryLoopState_exists {input : Guest.InputBlob} (entry : BaselineRuntimeEntry input) :
    ∃ base capacity, loopToWordStateRelHOLExact
      (entryLoopState entry base capacity) (entryFrontendState entry) := by
  obtain ⟨base,capacity,heap,length⟩ := entryFrontendState_heap_words entry
  exact ⟨base,capacity,entryLoopState_related entry base capacity heap length⟩

#print axioms entryFrontendState_heap_words
#print axioms entryLoopState_related
#print axioms entryLoopState_exists
end InitECandidate.Runtime
