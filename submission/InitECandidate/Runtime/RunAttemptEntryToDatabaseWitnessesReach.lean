import InitECandidate.Runtime.RunAttemptEntryToDatabaseReach
import InitECandidate.Runtime.RunAttemptDatabaseWitnesses
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
theorem run_attempt_entry_to_database_witnesses_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
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
    (nodeArray nodeCount codeArray codeCount : BitVec 64)
    (nodes : WitnessArrayLinked s si 40 48 nodeArray nodeCount input inputLength heap)
    (codes : WitnessArrayLinked s si 56 64 codeArray codeCount input inputLength heap)
    (nodesAbove : nodeCount.toNat = 0 ∨ ceiling ≤ nodeArray.toNat)
    (codesAbove : codeCount.toNat = 0 ∨ ceiling ≤ codeArray.toNat)
    (budget : validateHeadersBodyCost inputLimit + 1 ≤ s.clock) :
    Reaches s (runAttemptAt 0)
      (fun final => (∃ validated : PanSemStateFiniteExact 64 F, ∃ parent : BitVec 64,
        RunAttemptHeaderValidationFacts (setVarHOLFinite (ofString "pl") (.val (.word payload)) s) validated si array count input inputLength scratch frame heap keccakState keccakPad ceiling ∧
        count ≠ 0 ∧ final = setGlobalHOLFinite (ofString "block_hashes_n") (.val (.word count))
          (setGlobalHOLFinite (ofString "block_hashes") (.val (.word (allocationEnd heap (validateHeadersHsSize count))))
            (setVarHOLFinite (ofString "parent") (.val (.word parent))
              (setVarHOLFinite (ofString "nh") (.val (.word count)) validated)))) ∧
        (∃ finalHeap : BitVec 64, final.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
          heap.toNat ≤ finalHeap.toNat ∧ finalHeap.toNat ≤ 33806089496 ∧ finalHeap.toNat % 8 = 0 ∧
          WitnessArrayLinked final si 40 48 nodeArray nodeCount input inputLength finalHeap ∧
          WitnessArrayLinked final si 56 64 codeArray codeCount input inputLength finalHeap ∧
          (∀ address : BitVec 64, finalHeap.toNat ≤ address.toNat → address.toNat < 33806089496 →
            final.memaddrs address)))
      (validateHeadersBodyCost inputLimit + 1) (runAttemptAt 9) := by
  have reached := run_attempt_entry_to_database_reaches s si payload array count input inputLength scratch frame heap
    keccakState keccakPad ceiling inputLimit siDomain siCell inputBound inputCap inputAfter tableAbove inputBefore
    orderedFrame framePositive scratchBelow ceilingAligned stateBelow padBelow atSi linked scratchGlobal frameGlobal
    stateGlobal padGlobal arena heapArena heapGlobal heapBound code recordAbove recordBefore budget
  apply reaches_mono s (runAttemptAt 0) (runAttemptAt 9) _ _ _ _ (Nat.le_refl _) _ reached
  intro final evidence
  refine ⟨evidence,?_⟩
  obtain ⟨validated,parent,facts,nonempty,same⟩ := evidence
  subst final
  let entry := setVarHOLFinite (ofString "pl") (.val (.word payload)) s
  have entryNodes := nodes.after_frame s entry si 40 48 nodeArray nodeCount input inputLength heap rfl rfl
  have entryCodes := codes.after_frame s entry si 56 64 codeArray codeCount input inputLength heap rfl rfl
  exact facts.database_witnesses entry validated si array count input inputLength scratch frame heap keccakState
    keccakPad parent ceiling nodeArray nodeCount codeArray codeCount entryNodes entryCodes recordAbove recordBefore
    nodesAbove codesAbove

#print axioms run_attempt_entry_to_database_witnesses_reaches
end InitECandidate.Runtime
