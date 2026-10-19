import InitECandidate.Runtime.EndpointFrontendNative
import InitECandidate.Runtime.BaselineLoopCode
import InitECandidate.Runtime.BaselineNativeOutcomes
import InitECandidate.Runtime.SelectedStackFields
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Compiler.Backend

theorem endpointFrontendState_heap_words {input : Guest.InputBlob}
    (entry : EndpointRuntimeEntry input endpoint) :
    ∃ base capacity : BitVec 64,
      (endpointFrontendState entry).store.lookup .currHeap = some (.word base) ∧
      (endpointFrontendState entry).store.lookup .heapLength = some (.word capacity) := by
  obtain ⟨base,capacity,heap,length⟩ := StackRemove.selected_heap_words _ _ _ _ _ _ _ _ _ _ _ entry.selection
  refine ⟨base,capacity,?_,?_⟩
  · change (entry.source.store.eraseEq .handler).lookup .currHeap = _
    simpa [HolFiniteMapExact.lookup_eraseEq,FDOMSUB_HOL] using heap
  · change (entry.source.store.eraseEq .handler).lookup .heapLength = _
    simpa [HolFiniteMapExact.lookup_eraseEq,FDOMSUB_HOL] using length

/-- Exact Loop carrier matching all observable fields of frontend Word entry. -/
noncomputable def endpointLoopState {input : Guest.InputBlob} (entry : EndpointRuntimeEntry input endpoint)
    (base capacity : BitVec 64) : LoopSemStateFiniteExact 64 Guest.HostMemory where
  locals := .ln
  globals := HolFiniteMapExact.empty
  memory := (endpointFrontendState entry).memory
  mdomain := (endpointFrontendState entry).mdomain
  shMdomain := (endpointFrontendState entry).shMdomain
  clock := (endpointFrontendState entry).clock
  code := sptFromAList FrontendStages.pass4
  be := (endpointFrontendState entry).be
  ffi := (endpointFrontendState entry).ffi
  baseAddr := base
  topAddr := base + 2 * capacity

theorem endpointLoopState_related {input : Guest.InputBlob}
    (entry : EndpointRuntimeEntry input endpoint) (base capacity : BitVec 64)
    (heap : (endpointFrontendState entry).store.lookup .currHeap = some (.word base))
    (length : (endpointFrontendState entry).store.lookup .heapLength = some (.word capacity)) :
    loopToWordStateRelHOLExact (endpointLoopState entry base capacity) (endpointFrontendState entry) := by
  refine ⟨capacity,rfl,rfl,rfl,rfl,rfl,rfl,heap,length,rfl,?_,baseline_loop_word_codeRel⟩
  intro name value lookup
  change HolFiniteMapExact.empty.lookup name = some value at lookup
  simp [HolFiniteMapExact.empty] at lookup

/-- Actual initialization supplies a related Loop state without extra heap or
code assumptions. Earlier frontend passes must still relate their state to it. -/
theorem endpointLoopState_exists {input : Guest.InputBlob} (entry : EndpointRuntimeEntry input endpoint) :
    ∃ base capacity, loopToWordStateRelHOLExact
      (endpointLoopState entry base capacity) (endpointFrontendState entry) := by
  obtain ⟨base,capacity,heap,length⟩ := endpointFrontendState_heap_words entry
  exact ⟨base,capacity,endpointLoopState_related entry base capacity heap length⟩

#print axioms endpointFrontendState_heap_words
#print axioms endpointLoopState_related
#print axioms endpointLoopState_exists
end InitECandidate.Runtime
