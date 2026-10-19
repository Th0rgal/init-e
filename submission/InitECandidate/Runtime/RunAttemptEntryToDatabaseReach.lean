import InitECandidate.Runtime.RunAttemptHeadersToParentReach
import InitECandidate.Runtime.RunAttemptInitialHeadersBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
/-- The actual source entry through the first database-build call site.
All validation facts are retained at its real call-entry state. -/
theorem run_attempt_entry_to_database_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si payload array count input inputLength scratch frame heap keccakState keccakPad : BitVec 64)
    (ceiling inputLimit : Nat)
    (siDomain : s.memaddrs (si + (0#64)))
    (siCell : s.memory (si + (0#64)) = .word payload)
    (inputBound : inputLength.toNat ≤ inputLimit) (inputCap : inputLimit ≤ 134217712)
    (inputAfter : ceiling ≤ input.toNat) (tableAbove : ceiling ≤ array.toNat)
    (inputBefore : input.toNat + inputLength.toNat ≤ heap.toNat)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (ceilingAligned : ceiling % 8 = 0) (stateBelow : keccakState.toNat + 200 ≤ ceiling)
    (padBelow : keccakPad.toNat + 136 ≤ ceiling)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word si)))
    (linked : WitnessArrayLinked s si 72 80 array count input inputLength heap)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (stateGlobal : s.globals.lookup (ofString "keccak_st") = some (.val (.word keccakState)))
    (padGlobal : s.globals.lookup (ofString "keccak_pad") = some (.val (.word keccakPad)))
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (heapArena : ∀ address : BitVec 64, heap.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (heapGlobal : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode)
    (recordAbove : ceiling ≤ si.toNat) (recordBefore : si.toNat + 88 ≤ heap.toNat)
    (budget : validateHeadersBodyCost inputLimit + 1 ≤ s.clock) :
    Reaches s (runAttemptAt 0)
      (fun final => ∃ validated : PanSemStateFiniteExact 64 F, ∃ parent : BitVec 64,
        RunAttemptHeaderValidationFacts (setVarHOLFinite (ofString "pl") (.val (.word payload)) s) validated si array count input inputLength scratch frame heap keccakState keccakPad ceiling ∧
        count ≠ 0 ∧ final = setGlobalHOLFinite (ofString "block_hashes_n") (.val (.word count))
          (setGlobalHOLFinite (ofString "block_hashes") (.val (.word (allocationEnd heap (validateHeadersHsSize count))))
            (setVarHOLFinite (ofString "parent") (.val (.word parent))
              (setVarHOLFinite (ofString "nh") (.val (.word count)) validated))))
      (validateHeadersBodyCost inputLimit + 1) (runAttemptAt 9) := by
  have initial := run_attempt_initial_state_reaches s si payload atSi siDomain siCell
  have combined := reaches_trans s (runAttemptAt 0) (runAttemptAt 2) (runAttemptAt 9)
    (fun next => next = setVarHOLFinite (ofString "pl") (.val (.word payload)) s)
    (fun final => ∃ validated : PanSemStateFiniteExact 64 F, ∃ parent : BitVec 64,
        RunAttemptHeaderValidationFacts (setVarHOLFinite (ofString "pl") (.val (.word payload)) s) validated si array count input inputLength scratch frame heap keccakState keccakPad ceiling ∧
        count ≠ 0 ∧ final = setGlobalHOLFinite (ofString "block_hashes_n") (.val (.word count))
          (setGlobalHOLFinite (ofString "block_hashes") (.val (.word (allocationEnd heap (validateHeadersHsSize count))))
            (setVarHOLFinite (ofString "parent") (.val (.word parent))
              (setVarHOLFinite (ofString "nh") (.val (.word count)) validated)))) 0 (validateHeadersBodyCost inputLimit + 1) initial (by
      intro next same
      subst next
      have atSiNext : (setVarHOLFinite (ofString "pl") (.val (.word payload)) s).locals.lookup
          (ofString "si") = some (.val (.word si)) := by
        simpa (config := {decide := true}) [setVarHOLFinite,FUPDATE] using atSi
      have linkedNext := linked.after_frame s (setVarHOLFinite (ofString "pl") (.val (.word payload)) s)
        si 72 80 array count input inputLength heap rfl rfl
      exact run_attempt_headers_to_database_reaches _ si array count input inputLength scratch frame heap
        keccakState keccakPad ceiling inputLimit inputBound inputCap inputAfter tableAbove inputBefore orderedFrame
        framePositive scratchBelow ceilingAligned stateBelow padBelow atSiNext linkedNext scratchGlobal frameGlobal
        stateGlobal padGlobal arena heapArena heapGlobal heapBound code recordAbove recordBefore budget)
  simpa only [Nat.zero_add] using combined

#print axioms run_attempt_entry_to_database_reaches
end InitECandidate.Runtime
