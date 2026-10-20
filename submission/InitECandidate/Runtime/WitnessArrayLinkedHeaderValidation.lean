import InitECandidate.Runtime.RunAttemptHeadersToParentReach
import InitECandidate.Runtime.WitnessArrayLinkedWindow
/-!
The decoder's witness-array link survives real nonzero header validation.

The initial link `WitnessArrayLinked s si first second array count input length heap` describes the
canonically decoded witness record at `si`.  Header validation writes only above the old live heap and
never changes the memory domain, so the link survives: `RunAttemptHeaderValidationFacts` supplies both
the exact domain `ready.memaddrs = s.memaddrs` and the ready memory frame on `[ceiling, oldHeap)`,
which is exactly the window the link reads, and it also supplies the typed monotone `finalHeap`.

The two steps below are generic (no runtime or frame callback, no assumption about later code):

* `witness_linked_of_header_validation_facts` - caller state to the state after the real
  `validate_headers` call, at the typed `finalHeap`.
* `witness_linked_of_final_state` - any later state that only rewrites locals and globals (the
  `nh`/`parent`/`block_hashes`/`block_hashes_n` prefix) keeps the link unchanged.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- **The link survives the real header validation.**  Given the checked nonzero header validation
facts for the caller state `s` (typed `finalHeap`, exact domain, ready memory frame on
`[ceiling, heap)`), the original decoder link, and the window premises that both record cells and the
array itself sit inside `[ceiling, heap)`, the header pointer and the header count still read the same
in the state `ready` reached by the real `validate_headers` call, and the recorded array end is below
the typed monotone `finalHeap`. -/
theorem witness_linked_of_header_validation_facts {F : Type} (s ready : PanSemStateFiniteExact 64 F)
    (si first second array count input inputLength scratch frame heap keccakState keccakPad : BitVec 64)
    (ceiling : Nat)
    (facts : RunAttemptHeaderValidationFacts s ready si array count input inputLength scratch frame heap
      keccakState keccakPad ceiling)
    (linked : WitnessArrayLinked s si first second array count input inputLength heap)
    (pointerAbove : ceiling ≤ (si + first).toNat)
    (pointerBefore : (si + first).toNat < heap.toNat)
    (countAbove : ceiling ≤ (si + second).toNat)
    (countBefore : (si + second).toNat < heap.toNat)
    (arrayAbove : ceiling ≤ array.toNat) :
    ∃ finalHeap : BitVec 64,
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
      heap.toNat ≤ finalHeap.toNat ∧ finalHeap.toNat ≤ 33806089496 ∧
      WitnessArrayLinked ready si first second array count input inputLength finalHeap := by
  obtain ⟨value,bodyPost,bodyRun,localsUpdate,readyMemory,readyGlobals,readyDomain,readyCode,valueShape,
    atVh,countBound,⟨finalHeap,heapGlobal,heapMonotone,heapCapped,_,_,frame⟩,scratchGlobal,frameGlobal,
    stateGlobal,padGlobal,memoryFrame,tableSlice,rest⟩ := facts
  refine ⟨finalHeap,heapGlobal,heapMonotone,heapCapped,?_⟩
  refine WitnessArrayLinked.after_memory_between s ready si first second array count input inputLength
    heap finalHeap ceiling linked pointerAbove pointerBefore countAbove countBefore arrayAbove
    heapMonotone readyDomain ?_
  intro address above below
  exact memoryFrame address above below

#print axioms witness_linked_of_header_validation_facts

/-- **A locals-and-globals-only continuation keeps the link.**  Header validation's later caller
prefix only declares locals and assigns globals, so any state `post` with the same memory and the same
memory domain as the validated state carries the same witness-array link. -/
theorem witness_linked_of_final_state {F : Type} (ready post : PanSemStateFiniteExact 64 F)
    (si first second array count input inputLength finalHeap : BitVec 64)
    (linked : WitnessArrayLinked ready si first second array count input inputLength finalHeap)
    (domain : post.memaddrs = ready.memaddrs) (memory : post.memory = ready.memory) :
    WitnessArrayLinked post si first second array count input inputLength finalHeap :=
  linked.after_frame ready post si first second array count input inputLength finalHeap domain memory

#print axioms witness_linked_of_final_state

/-- **The link survives the exact `nh`/`parent`/`block_hashes`/`block_hashes_n` prefix.**
Instantiating the locals-and-globals step at the actual final caller state recorded by the selected
root reach: declaring `nh`, declaring `parent` and assigning the two `block_hashes` globals never
touches memory or the memory domain, so the decoder's witness-array link still holds there, against
the typed monotone final heap. -/
theorem witness_linked_of_header_validation_final {F : Type} (s ready : PanSemStateFiniteExact 64 F)
    (si first second array count input inputLength scratch frame heap keccakState keccakPad : BitVec 64)
    (parent liveHeap : BitVec 64) (ceiling : Nat)
    (facts : RunAttemptHeaderValidationFacts s ready si array count input inputLength scratch frame heap
      keccakState keccakPad ceiling)
    (linked : WitnessArrayLinked s si first second array count input inputLength heap)
    (pointerAbove : ceiling ≤ (si + first).toNat)
    (pointerBefore : (si + first).toNat < heap.toNat)
    (countAbove : ceiling ≤ (si + second).toNat)
    (countBefore : (si + second).toNat < heap.toNat)
    (arrayAbove : ceiling ≤ array.toNat) :
    ∃ finalHeap : BitVec 64,
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
      heap.toNat ≤ finalHeap.toNat ∧ finalHeap.toNat ≤ 33806089496 ∧
      WitnessArrayLinked
        (setGlobalHOLFinite (ofString "block_hashes_n") (.val (.word count))
          (setGlobalHOLFinite (ofString "block_hashes") (.val (.word liveHeap))
            (setVarHOLFinite (ofString "parent") (.val (.word parent))
              (setVarHOLFinite (ofString "nh") (.val (.word count)) ready))))
        si first second array count input inputLength finalHeap := by
  obtain ⟨finalHeap,heapGlobal,heapMonotone,heapCapped,linkedReady⟩ :=
    witness_linked_of_header_validation_facts s ready si first second array count input inputLength
      scratch frame heap keccakState keccakPad ceiling facts linked pointerAbove pointerBefore
      countAbove countBefore arrayAbove
  refine ⟨finalHeap,heapGlobal,heapMonotone,heapCapped,?_⟩
  exact witness_linked_of_final_state ready _ si first second array count input inputLength finalHeap
    linkedReady (by simp [setVarHOLFinite,setGlobalHOLFinite]) (by simp [setVarHOLFinite,setGlobalHOLFinite])

#print axioms witness_linked_of_header_validation_final
end InitECandidate.Runtime
