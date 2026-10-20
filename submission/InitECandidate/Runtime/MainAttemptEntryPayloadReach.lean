import InitECandidate.Runtime.MainVmEntryPayloadReach
import InitECandidate.Runtime.AttemptWrapperGenericBound
/-!
The main VM-entry reach, carried into the real wrapper call context of `run_attempt`.

`attemptEntry s si depth` is the actual wrapper call-entry state: it rewrites only the locals (the
callee's parameter vector, including the typed `si`) and the clock, so memory, globals, the memory
domain and the code are untouched (`attemptEntry_context`, all definitional).  Therefore every piece of
metadata the main bridge exports at the reached state also holds at the attempt-entry context, at depth
`depth`, with **no clock budget spent**: this is a pure transport, not an execution step.  Only the later
runtime use of the `run_attempt` prefix needs the extra nine ticks.

Ceiling used by the state_init caller is the corrected concrete `2713731432`.

Depth.  The theorem is stated for an arbitrary `depth`, because the transport is valid for any depth.
The reached state `post` is `mainAt 23`, i.e. still *before* main's verify call, so the real entry of
`run_attempt` inside main is depth **nine**: main's verify call site (one entry level) plus the wrapper's
own eight levels.  Depth eight is only the offset relative to the verify callee, not the main context.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- **Main's decoded witness record stays readable at the wrapper's attempt-entry context.**  A
faithful strengthening of `main_vm_entry_payload_reach`: the same existential data and side conditions,
and the `mainAt 21 -> mainAt 23` predicate additionally records, at `attemptEntry post si depth`, the three
decoder witness links, the typed `si`, the readable decoded payload cell `si+0` with its domain, the
exact memory domain and original code, and the initialized non-heap globals.  Memory, globals, domain
and code are untouched by the attempt entry, and the typed `si` is the callee's own parameter, so no
clock budget is consumed by this transport. -/
theorem main_attempt_entry_payload_reach {F : Type} (state ready decodedState : PanSemStateFiniteExact 64 F)
    (depth : Nat)
    (code : state.code = originalRuntimeCode)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 →
      2713714688 ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (valid : MainDecoderEntry state ready)
    (run : evaluateHOLFiniteState ready mainStatelessCall = (none,decodedState))
    (budget : 2 + (htrNewPayloadBodyCost + 1) ≤ decodedState.clock) :
    ∃ si rootHeap payload array count codes codeCount headers headerCount length : BitVec 64,
      rootHeap.toNat≤5000000000 ∧ (allocationEnd rootHeap 32).toNat≤5000000040 ∧
      length.toNat≤134217712 ∧ 2713731432+length.toNat≤si.toNat ∧ si.toNat+88≤rootHeap.toNat ∧
      (count = 0 ∨ si.toNat + 88 ≤ array.toNat) ∧
      (codeCount = 0 ∨ si.toNat + 88 ≤ codes.toNat) ∧
      (headerCount = 0 ∨ si.toNat + 88 ≤ headers.toNat) ∧
      2713715344 ≤ si.toNat ∧ (allocationEnd rootHeap 32).toNat % 8 = 0 ∧
      Reaches decodedState (mainAt 21)
        (fun post =>
          WitnessArrayLinked post si 40 48 array count 2713731432 length (allocationEnd rootHeap 32) ∧
          WitnessArrayLinked post si 56 64 codes codeCount 2713731432 length (allocationEnd rootHeap 32) ∧
          WitnessArrayLinked post si 72 80 headers headerCount 2713731432 length (allocationEnd rootHeap 32) ∧
          post.locals.lookup (ofString "si") = some (.val (.word si)) ∧
          post.locals.lookup (ofString "root") = some (.val (.word rootHeap)) ∧
          post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd rootHeap 32))) ∧
          (∀ key, key≠ofString "heap_ptr"→post.globals.lookup key=(allInitializerGlobals state.globals).lookup key) ∧
          post.memaddrs = decodedState.memaddrs ∧ post.code = originalRuntimeCode ∧
          post.memaddrs (si + (0#64)) ∧ post.memory (si + (0#64)) = .word payload ∧
          WitnessArrayLinked (attemptEntry post si depth) si 40 48 array count 2713731432 length
            (allocationEnd rootHeap 32) ∧
          WitnessArrayLinked (attemptEntry post si depth) si 56 64 codes codeCount 2713731432 length
            (allocationEnd rootHeap 32) ∧
          WitnessArrayLinked (attemptEntry post si depth) si 72 80 headers headerCount 2713731432 length
            (allocationEnd rootHeap 32) ∧
          (attemptEntry post si depth).locals.lookup (ofString "si") = some (.val (.word si)) ∧
          (attemptEntry post si depth).memaddrs (si + (0#64)) ∧
          (attemptEntry post si depth).memory (si + (0#64)) = .word payload ∧
          (attemptEntry post si depth).globals.lookup (ofString "heap_ptr") =
            some (.val (.word (allocationEnd rootHeap 32))) ∧
          (attemptEntry post si depth).memaddrs = decodedState.memaddrs ∧
          (attemptEntry post si depth).code = originalRuntimeCode ∧
          (∀ key, key≠ofString "heap_ptr"→
            (attemptEntry post si depth).globals.lookup key=(allInitializerGlobals state.globals).lookup key))
        (2 + (htrNewPayloadBodyCost + 1)) (mainAt 23) := by
  obtain ⟨si,rootHeap,payload,array,count,codes,codeCount,headers,headerCount,length,
    rootSmall,allocationUpper,lengthBound,recordAbove,recordExtent,arrayAbove,codesAbove,headersAbove,
    lower,reach⟩ := main_vm_entry_payload_reach state ready decodedState code arena valid run budget
  have heapAligned : (allocationEnd rootHeap 32).toNat % 8 = 0 := by
    rw [allocationEnd_eq_align,panByteAlign_toNat64]
    have := Nat.mul_mod_right 8 (BitVec.toNat (rootHeap + (32#64) + (7#64)) / 8)
    simpa [Nat.mul_comm] using this
  refine ⟨si,rootHeap,payload,array,count,codes,codeCount,headers,headerCount,length,
    rootSmall,allocationUpper,lengthBound,recordAbove,recordExtent,arrayAbove,codesAbove,headersAbove,
    lower,heapAligned,?_⟩
  refine reaches_mono decodedState (mainAt 21) (mainAt 23) _ _ _ _ (le_refl _) ?_ reach
  intro post facts
  obtain ⟨stateLinked,codesLinked,headersLinked,siLocal,rootLocal,heapGlobal,initialized,domain,codeEq,
    payloadDomain,payloadCell⟩ := facts
  exact ⟨stateLinked,codesLinked,headersLinked,siLocal,rootLocal,heapGlobal,initialized,domain,codeEq,
    payloadDomain,payloadCell,
    stateLinked.after_frame post (attemptEntry post si depth) si 40 48 array count 2713731432 length
      (allocationEnd rootHeap 32) rfl rfl,
    codesLinked.after_frame post (attemptEntry post si depth) si 56 64 codes codeCount 2713731432 length
      (allocationEnd rootHeap 32) rfl rfl,
    headersLinked.after_frame post (attemptEntry post si depth) si 72 80 headers headerCount 2713731432 length
      (allocationEnd rootHeap 32) rfl rfl,
    attemptEntry_si post si 8,
    by simpa [attemptEntry] using payloadDomain, by simpa [attemptEntry] using payloadCell,
    by simpa [attemptEntry] using heapGlobal,
    by simpa [attemptEntry] using domain, by simpa [attemptEntry] using codeEq,
    by simpa [attemptEntry] using initialized⟩



#print axioms main_attempt_entry_payload_reach
end InitECandidate.Runtime
