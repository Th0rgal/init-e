import InitECandidate.Runtime.RunAttemptEntryToSelectedRootReach
import InitECandidate.Runtime.WitnessArrayLinkedHeaderValidation
/-!
The actual `run_attempt` entry reaches its selected parent root while the decoder's own witness
record still reads the same.

The authoritative selected-root reach `run_attempt_entry_to_selected_root_reaches` already records the
validated state, the header-validation facts, the nonzero header count, the exact final state and the
parent/root/extent/hash-floor data.  Here we additionally carry the original decoder links of the
caller state - the state array at `si+40`/`si+48` and the code array at `si+56`/`si+64` - through the
real run:

* the `pl` local declaration is a locals-only step, so both links pass to the call site unchanged;
* the header-validation facts give the retained window `[ceiling, heap)`, the exact domain and the
  typed monotone live heap, so the corrected transport helper keeps both links up to the state after
  the header call;
* the `nh`/`parent`/`block_hashes`/`block_hashes_n` prefix only rewrites locals and globals.

The record's existentially quantified live heap is identified with the heap the final state actually
returns by lookup uniqueness on `heap_ptr`, so both links are stated at the **same** returned live heap.
No runtime or frame callback is introduced, and every original consequence of the selected-root reach
is retained.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A record cell `si + offset` with `offset < 88` lies strictly inside the retained window
`[ceiling, heap)` once the record itself does. -/
theorem record_cell_window (si heap offset : BitVec 64) (ceiling : Nat)
    (offsetSmall : offset.toNat < 88) (recordAbove : ceiling ≤ si.toNat)
    (recordBefore : si.toNat + 88 ≤ heap.toNat) (heapCapped : heap.toNat ≤ 33806089496) :
    ceiling ≤ (si + offset).toNat ∧ (si + offset).toNat < heap.toNat := by
  have hcap : (33806089496 : Nat) < 2 ^ 64 := by decide
  have addNat : (si + offset).toNat = si.toNat + offset.toNat := by
    rw [BitVec.toNat_add]
    have small : si.toNat + offset.toNat < 2 ^ 64 := by omega
    exact Nat.mod_eq_of_lt small
  constructor <;> omega

#print axioms record_cell_window

/-- **The entry reaches the selected parent root with both decoder witness links intact.**  Every
consequence of the authoritative selected-root reach is kept, and additionally the state array link
(`si+40`/`si+48`) and the code array link (`si+56`/`si+64`) hold in the exact final state at the very
same returned live heap, together with the typed `si`, the original code, the original domain and heap
alignment.  Each witness pointer only needs a lower bound when that witness array is nonempty. -/
theorem run_attempt_entry_all_witness_selected_root_reaches {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (si payload array count input inputLength scratch frame heap keccakState keccakPad : BitVec 64)
    (stateArray stateCount codeArray codeCount : BitVec 64)
    (ceiling inputLimit : Nat)
    (siDomain : s.memaddrs (si + (0#64)))
    (siCell : s.memory (si + (0#64)) = .word payload)
    (inputBound : inputLength.toNat ≤ inputLimit) (inputCap : inputLimit ≤ 134217712)
    (inputAfter : ceiling ≤ input.toNat) (tableAbove : ceiling ≤ array.toNat)
    (inputBefore : input.toNat + inputLength.toNat ≤ heap.toNat)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (ceilingAligned : ceiling % 8 = 0) (stateBelow : keccakState.toNat + 200 ≤ ceiling)
    (padBelow : keccakPad.toNat + 136 ≤ ceiling)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word si)))
    (linked : WitnessArrayLinked s si 72 80 array count input inputLength heap)
    (stateLinked : WitnessArrayLinked s si 40 48 stateArray stateCount input inputLength heap)
    (stateArrayAbove : stateCount.toNat = 0 ∨ ceiling ≤ stateArray.toNat)
    (codeLinked : WitnessArrayLinked s si 56 64 codeArray codeCount input inputLength heap)
    (codeArrayAbove : codeCount.toNat = 0 ∨ ceiling ≤ codeArray.toNat)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (stateGlobal : s.globals.lookup (ofString "keccak_st") = some (.val (.word keccakState)))
    (padGlobal : s.globals.lookup (ofString "keccak_pad") = some (.val (.word keccakPad)))
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling →
      s.memaddrs address)
    (heapArena : ∀ address : BitVec 64, heap.toNat ≤ address.toNat → address.toNat < 33806089496 →
      s.memaddrs address)
    (heapGlobal : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapUpper : heap.toNat ≤ 33805910000)
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode)
    (recordAbove : ceiling ≤ si.toNat) (recordBefore : si.toNat + 88 ≤ heap.toNat)
    (budget : validateHeadersBodyCost inputLimit + 1 ≤ s.clock) :
    Reaches s (runAttemptAt 0)
      (fun final => ∃ validated : PanSemStateFiniteExact 64 F, ∃ liveHeap parent root : BitVec 64,
        RunAttemptHeaderValidationFacts (setVarHOLFinite (ofString "pl") (.val (.word payload)) s)
          validated si array count input inputLength scratch frame heap keccakState keccakPad ceiling ∧
        count ≠ 0 ∧
        final = setGlobalHOLFinite (ofString "block_hashes_n") (.val (.word count))
          (setGlobalHOLFinite (ofString "block_hashes")
            (.val (.word (allocationEnd heap (validateHeadersHsSize count))))
            (setVarHOLFinite (ofString "parent") (.val (.word parent))
              (setVarHOLFinite (ofString "nh") (.val (.word count)) validated))) ∧
        final.locals.lookup (ofString "parent") = some (.val (.word parent)) ∧
        final.globals.lookup (ofString "heap_ptr") = some (.val (.word liveHeap)) ∧
        final.memory (parent + (32#64)) = .word root ∧ final.memaddrs (parent + (32#64)) ∧
        parent.toNat + 248 ≤ liveHeap.toNat ∧
        (allocationEnd heap (validateHeadersHsSize count)).toNat + count.toNat * 32 + 32 ≤ parent.toNat ∧
        WitnessArrayLinked final si 40 48 stateArray stateCount input inputLength liveHeap ∧
        WitnessArrayLinked final si 56 64 codeArray codeCount input inputLength liveHeap ∧
        final.locals.lookup (ofString "si") = some (.val (.word si)) ∧
        final.code = originalRuntimeCode ∧ final.memaddrs = s.memaddrs ∧
        liveHeap.toNat % 8 = 0)
      (validateHeadersBodyCost inputLimit + 1) (runAttemptAt 9) := by
  have entry := run_attempt_entry_to_selected_root_reaches s si payload array count input inputLength
    scratch frame heap keccakState keccakPad ceiling inputLimit siDomain siCell inputBound inputCap
    inputAfter tableAbove inputBefore orderedFrame framePositive scratchBelow ceilingAligned stateBelow
    padBelow atSi linked scratchGlobal frameGlobal stateGlobal padGlobal arena heapArena heapGlobal
    heapUpper heapBound code recordAbove recordBefore budget
  refine reaches_mono s (runAttemptAt 0) (runAttemptAt 9) _ _ _ _ (Nat.le_refl _) ?_ entry
  intro final facts
  obtain ⟨validated,liveHeap,parent,root,headerFacts,nonzero,finalEq,parentLocal,heapPtr,rootCell,
    rootDomain,parentBelow,floorBelow⟩ := facts
  subst finalEq
  have stateAtCaller := stateLinked.after_frame s
    (setVarHOLFinite (ofString "pl") (.val (.word payload)) s) si 40 48 stateArray stateCount input
    inputLength heap rfl rfl
  have codeAtCaller := codeLinked.after_frame s
    (setVarHOLFinite (ofString "pl") (.val (.word payload)) s) si 56 64 codeArray codeCount input
    inputLength heap rfl rfl
  obtain ⟨cell40Above,cell40Before⟩ := record_cell_window si heap (40#64) ceiling (by decide)
    recordAbove recordBefore heapBound
  obtain ⟨cell48Above,cell48Before⟩ := record_cell_window si heap (48#64) ceiling (by decide)
    recordAbove recordBefore heapBound
  obtain ⟨cell56Above,cell56Before⟩ := record_cell_window si heap (56#64) ceiling (by decide)
    recordAbove recordBefore heapBound
  obtain ⟨cell64Above,cell64Before⟩ := record_cell_window si heap (64#64) ceiling (by decide)
    recordAbove recordBefore heapBound
  have factSource := headerFacts
  have factCopy := headerFacts
  obtain ⟨value,bodyPost,bodyRun,localsUpdate,readyMemory,readyGlobals,readyDomain,readyCode,valueShape,
    atVh,headerBound,⟨finalHeap,heapPtrValidated,heapMonotone,heapCapped,heapAligned,_,_⟩,scratchGlobal',
    frameGlobal',stateGlobal',padGlobal',memoryFrame,bodySlice,readySlice,pointerPrefix,siLocal⟩ :=
    factCopy
  obtain ⟨stateHeap,statePtr,_,_,stateFinalLink⟩ :=
    witness_linked_of_header_validation_final
      (setVarHOLFinite (ofString "pl") (.val (.word payload)) s) validated si 40 48 stateArray
      stateCount array count input inputLength scratch frame heap keccakState keccakPad parent
      (allocationEnd heap (validateHeadersHsSize count)) ceiling factSource stateAtCaller cell40Above
      cell40Before cell48Above cell48Before stateArrayAbove
  obtain ⟨codeHeap,codePtr,_,_,codeFinalLink⟩ :=
    witness_linked_of_header_validation_final
      (setVarHOLFinite (ofString "pl") (.val (.word payload)) s) validated si 56 64 codeArray
      codeCount array count input inputLength scratch frame heap keccakState keccakPad parent
      (allocationEnd heap (validateHeadersHsSize count)) ceiling factSource codeAtCaller cell56Above
      cell56Before cell64Above cell64Before codeArrayAbove
  have stateHeapEq : stateHeap = finalHeap := by
    have := statePtr.symm.trans heapPtrValidated
    exact Option.some.inj (by simpa using this)
  have codeHeapEq : codeHeap = finalHeap := by
    have := codePtr.symm.trans heapPtrValidated
    exact Option.some.inj (by simpa using this)
  have finalHeapPtr : (setGlobalHOLFinite (ofString "block_hashes_n") (.val (.word count))
        (setGlobalHOLFinite (ofString "block_hashes")
          (.val (.word (allocationEnd heap (validateHeadersHsSize count))))
          (setVarHOLFinite (ofString "parent") (.val (.word parent))
            (setVarHOLFinite (ofString "nh") (.val (.word count)) validated)))).globals.lookup
        (ofString "heap_ptr") = validated.globals.lookup (ofString "heap_ptr") := by
    simp (config := {decide := true}) [setVarHOLFinite,setGlobalHOLFinite,
      HolFiniteMapExact.lookup_update,FUPDATE]
  have liveEq : liveHeap = finalHeap := by
    have same : (some (.val (.word liveHeap)) : Option (ValueHOL 64)) =
        some (.val (.word finalHeap)) := by
      rw [← heapPtr,finalHeapPtr,heapPtrValidated]
    exact Option.some.inj (by simpa using same)
  refine ⟨validated,finalHeap,parent,root,factSource,nonzero,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [setVarHOLFinite,setGlobalHOLFinite]
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using parentLocal
  · rw [finalHeapPtr]
    exact heapPtrValidated
  · simpa [setVarHOLFinite,setGlobalHOLFinite] using rootCell
  · simpa [setVarHOLFinite,setGlobalHOLFinite] using rootDomain
  · exact liveEq ▸ parentBelow
  · exact floorBelow
  · exact stateHeapEq ▸ stateFinalLink
  · exact codeHeapEq ▸ codeFinalLink
  · simpa (config := {decide := true}) [setVarHOLFinite,setGlobalHOLFinite,
      HolFiniteMapExact.lookup_update,FUPDATE] using siLocal
  · exact readyCode.trans code
  · exact readyDomain
  · exact heapAligned

#print axioms run_attempt_entry_all_witness_selected_root_reaches
end InitECandidate.Runtime
