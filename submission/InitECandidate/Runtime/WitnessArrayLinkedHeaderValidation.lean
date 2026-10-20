import InitECandidate.Runtime.RunAttemptHeadersToParentReach
import InitECandidate.Runtime.WitnessArrayLinkedWindow
/-!
The decoder's witness-array link survives real header validation.

The header array and the original witness array are **different objects**: header validation reads its
own header array/count (the canonical decode's header table), while the decoder's witness record at
`si` carries its own array pointer and count.  Only the input bytes are common.  These helpers keep the
two fully separate:

* the facts are `RunAttemptHeaderValidationFacts s ready si headerArray headerCount input inputLength
  …` and supply the typed monotone `finalHeap`, the exact domain `ready.memaddrs = s.memaddrs` and the
  ready memory frame on `[ceiling, oldHeap)`;
* the link is `WitnessArrayLinked s si first second witnessArray witnessCount input inputLength heap`.

Because the witness array pointer may be the empty-array sentinel, the window assumption on it is
`witnessCount.toNat = 0 ∨ ceiling ≤ witnessArray.toNat`, handled by
`WitnessArrayLinked.after_memory_between_or_empty`.  The two record cells are always read, so they
carry the strict window assumptions.  No runtime or frame callback is used, and nothing is assumed
about later code.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- **The decoder's witness link survives the real header validation.**  The header array/count used
by validation and the witness array/count in the decoder's record are separate; the retained window
`[ceiling, heap)` keeps both record cells, and the witness array pointer only needs a lower bound when
the witness array is nonempty.  The state `ready` reached by the real `validate_headers` call therefore
still satisfies the original link, against the typed monotone `finalHeap`. -/
theorem witness_linked_of_header_validation_facts {F : Type} (s ready : PanSemStateFiniteExact 64 F)
    (si first second witnessArray witnessCount headerArray headerCount : BitVec 64)
    (input inputLength scratch frame heap keccakState keccakPad : BitVec 64)
    (ceiling : Nat)
    (facts : RunAttemptHeaderValidationFacts s ready si headerArray headerCount input inputLength scratch
      frame heap keccakState keccakPad ceiling)
    (linked : WitnessArrayLinked s si first second witnessArray witnessCount input inputLength heap)
    (pointerAbove : ceiling ≤ (si + first).toNat)
    (pointerBefore : (si + first).toNat < heap.toNat)
    (countAbove : ceiling ≤ (si + second).toNat)
    (countBefore : (si + second).toNat < heap.toNat)
    (arrayAbove : witnessCount.toNat = 0 ∨ ceiling ≤ witnessArray.toNat) :
    ∃ finalHeap : BitVec 64,
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
      heap.toNat ≤ finalHeap.toNat ∧ finalHeap.toNat ≤ 33806089496 ∧
      WitnessArrayLinked ready si first second witnessArray witnessCount input inputLength finalHeap := by
  obtain ⟨value,bodyPost,bodyRun,localsUpdate,readyMemory,readyGlobals,readyDomain,readyCode,valueShape,
    atVh,headerBound,⟨finalHeap,heapGlobal,heapMonotone,heapCapped,_,_,_⟩,scratchGlobal,frameGlobal,
    stateGlobal,padGlobal,memoryFrame,bodySlice,readySlice,pointerPrefix,siLocal⟩ := facts
  refine ⟨finalHeap,heapGlobal,heapMonotone,heapCapped,?_⟩
  refine WitnessArrayLinked.after_memory_between_or_empty s ready si first second witnessArray
    witnessCount input inputLength heap finalHeap ceiling linked pointerAbove pointerBefore countAbove
    countBefore arrayAbove heapMonotone readyDomain ?_
  intro address above below
  exact memoryFrame address above below

#print axioms witness_linked_of_header_validation_facts

/-- **A locals-and-globals-only continuation keeps the link.**  Validation's later caller prefix only
declares locals and assigns globals, so any state `post` with the same memory and the same memory
domain carries the same witness-array link. -/
theorem witness_linked_of_final_state {F : Type} (ready post : PanSemStateFiniteExact 64 F)
    (si first second witnessArray witnessCount input inputLength finalHeap : BitVec 64)
    (linked : WitnessArrayLinked ready si first second witnessArray witnessCount input inputLength
      finalHeap)
    (domain : post.memaddrs = ready.memaddrs) (memory : post.memory = ready.memory) :
    WitnessArrayLinked post si first second witnessArray witnessCount input inputLength finalHeap :=
  linked.after_frame ready post si first second witnessArray witnessCount input inputLength finalHeap
    domain memory

#print axioms witness_linked_of_final_state

/-- **The witness link survives the exact `nh`/`parent`/`block_hashes`/`block_hashes_n` prefix.**
Instantiating the locals-and-globals step at the actual final caller state recorded by the selected
root reach: declaring `nh` and `parent` from the **header** count and assigning the two
`block_hashes` globals (the second one from the header count, not the witness count) never touches
memory or the memory domain, so the decoder's witness link still holds there against `finalHeap`. -/
theorem witness_linked_of_header_validation_final {F : Type} (s ready : PanSemStateFiniteExact 64 F)
    (si first second witnessArray witnessCount headerArray headerCount : BitVec 64)
    (input inputLength scratch frame heap keccakState keccakPad : BitVec 64)
    (parent liveHeap : BitVec 64) (ceiling : Nat)
    (facts : RunAttemptHeaderValidationFacts s ready si headerArray headerCount input inputLength scratch
      frame heap keccakState keccakPad ceiling)
    (linked : WitnessArrayLinked s si first second witnessArray witnessCount input inputLength heap)
    (pointerAbove : ceiling ≤ (si + first).toNat)
    (pointerBefore : (si + first).toNat < heap.toNat)
    (countAbove : ceiling ≤ (si + second).toNat)
    (countBefore : (si + second).toNat < heap.toNat)
    (arrayAbove : witnessCount.toNat = 0 ∨ ceiling ≤ witnessArray.toNat) :
    ∃ finalHeap : BitVec 64,
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
      heap.toNat ≤ finalHeap.toNat ∧ finalHeap.toNat ≤ 33806089496 ∧
      WitnessArrayLinked
        (setGlobalHOLFinite (ofString "block_hashes_n") (.val (.word headerCount))
          (setGlobalHOLFinite (ofString "block_hashes") (.val (.word liveHeap))
            (setVarHOLFinite (ofString "parent") (.val (.word parent))
              (setVarHOLFinite (ofString "nh") (.val (.word headerCount)) ready))))
        si first second witnessArray witnessCount input inputLength finalHeap := by
  obtain ⟨finalHeap,heapGlobal,heapMonotone,heapCapped,linkedReady⟩ :=
    witness_linked_of_header_validation_facts s ready si first second witnessArray witnessCount
      headerArray headerCount input inputLength scratch frame heap keccakState keccakPad ceiling facts
      linked pointerAbove pointerBefore countAbove countBefore arrayAbove
  refine ⟨finalHeap,heapGlobal,heapMonotone,heapCapped,?_⟩
  exact witness_linked_of_final_state ready _ si first second witnessArray witnessCount input inputLength
    finalHeap linkedReady (by simp [setVarHOLFinite,setGlobalHOLFinite])
    (by simp [setVarHOLFinite,setGlobalHOLFinite])

#print axioms witness_linked_of_header_validation_final
end InitECandidate.Runtime
