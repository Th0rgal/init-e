import InitECandidate.Runtime.RunAttemptTwoDatabaseValuesReach
import InitECandidate.Runtime.RunAttemptEntryToTwoDatabaseWitnesses
import InitECandidate.Runtime.RunAttemptTwoDatabaseTablesReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
theorem run_attempt_entry_to_two_database_values {F : Type} (s : PanSemStateFiniteExact 64 F)
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
    (output : BitVec 64)
    (outputGlobal : s.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)))
    (outputAligned : output.toNat % 8 = 0) (outputBelow : output.toNat + 32 ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (heapArena : ∀ address : BitVec 64, heap.toNat ≤ address.toNat → address.toNat < 33806089496 →
      s.memaddrs address)
    (heapGlobal : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode)
    (recordAbove : ceiling ≤ si.toNat) (recordBefore : si.toNat + 88 ≤ heap.toNat)
    (nodeArray nodeCount codeArray codeCount : BitVec 64)
    (nodes : WitnessArrayLinked s si 40 48 nodeArray nodeCount input inputLength heap)
    (codes : WitnessArrayLinked s si 56 64 codeArray codeCount input inputLength heap)
    (nodesAbove : nodeCount.toNat = 0 ∨ ceiling ≤ nodeArray.toNat)
    (codesAbove : codeCount.toNat = 0 ∨ ceiling ≤ codeArray.toNat)
    (windows₁ : nodeCount ≠ 0 → keccakState.toNat + 200 ≤ nodeArray.toNat ∧
      keccakPad.toNat + 136 ≤ nodeArray.toNat ∧ output.toNat + 32 ≤ nodeArray.toNat)
    (windows₂ : codeCount ≠ 0 → keccakState.toNat + 200 ≤ codeArray.toNat ∧
      keccakPad.toNat + 136 ≤ codeArray.toNat ∧ output.toNat + 32 ≤ codeArray.toNat)
    (budget : (validateHeadersBodyCost inputLimit + 1) + 2 * nodedbInputCallCost inputLimit ≤ s.clock) :
    Reaches s (runAttemptAt 0)
      (fun final => ∃ ready validated : PanSemStateFiniteExact 64 F, ∃ parent firstHeap midHeap finalHeap : BitVec 64,
        RunAttemptHeaderValidationFacts (setVarHOLFinite (ofString "pl") (.val (.word payload)) s) validated
          si array count input inputLength scratch frame heap keccakState keccakPad ceiling ∧
        count ≠ 0 ∧
        ready = runAttemptDatabaseState validated count parent (allocationEnd heap (validateHeadersHsSize count)) ∧
        heap.toNat ≤ firstHeap.toNat ∧
        final.locals = (ready.locals.update (ofString "nodedb",.val (.word firstHeap))).update
          (ofString "codedb",.val (.word midHeap)) ∧
        final.memaddrs = ready.memaddrs ∧ final.code = s.code ∧ final.be = ready.be ∧
        final.globals.lookup (ofString "keccak_st") = some (.val (.word keccakState)) ∧
        final.globals.lookup (ofString "keccak_pad") = some (.val (.word keccakPad)) ∧
        final.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)) ∧
        final.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
        firstHeap.toNat ≤ midHeap.toNat ∧ midHeap.toNat ≤ finalHeap.toNat ∧
        finalHeap.toNat % 8 = 0 ∧ finalHeap.toNat ≤ 33806089496 ∧
        HashTableValuesIn firstHeap (NodedbSliceTargets nodeArray nodeCount) final ∧
        HashTableValuesIn midHeap (NodedbSliceTargets codeArray codeCount) final ∧
        NodedbTableAt final firstHeap finalHeap nodeCount ∧ NodedbTableAt final midHeap finalHeap codeCount ∧
        (∀ a : BitVec 64, a.toNat % 8 = 0 → finalHeap.toNat ≤ a.toNat → a.toNat < 33806089496 → final.memaddrs a) ∧
        (∀ w : BitVec 64, w.toNat < firstHeap.toNat → ¬ MWin keccakState 200 w → ¬ MWin keccakPad 136 w →
          ¬ MWin output 32 w → final.memory w = ready.memory w))
      ((validateHeadersBodyCost inputLimit + 1) + 2 * nodedbInputCallCost inputLimit) (runAttemptAt 11) := by
  have entry := run_attempt_entry_to_database_witnesses_reaches s si payload array count input inputLength scratch
    frame heap keccakState keccakPad ceiling inputLimit siDomain siCell inputBound inputCap inputAfter tableAbove
    inputBefore orderedFrame framePositive scratchBelow ceilingAligned stateBelow padBelow atSi linked scratchGlobal
    frameGlobal stateGlobal padGlobal arena heapArena heapGlobal heapBound code recordAbove recordBefore
    nodeArray nodeCount codeArray codeCount nodes codes nodesAbove codesAbove (by omega)
  refine reaches_trans_budget s (runAttemptAt 0) (runAttemptAt 9) (runAttemptAt 11) _ _
    (validateHeadersBodyCost inputLimit + 1) (2 * nodedbInputCallCost inputLimit) budget entry ?_
  intro ready facts tailBudget
  obtain ⟨⟨validated,parent,validFacts,nonempty,same⟩,
    ⟨firstHeap,atH,monotone,bounded,alHeap,linkedNodes,linkedCodes,live⟩⟩ := facts
  let next := runAttemptDatabaseState validated count parent (allocationEnd heap (validateHeadersHsSize count))
  have readyEq : ready = next := same
  have atHNext : next.globals.lookup (ofString "heap_ptr") = some (.val (.word firstHeap)) := readyEq ▸ atH
  have linkedNodesNext : WitnessArrayLinked next si 40 48 nodeArray nodeCount input inputLength firstHeap :=
    readyEq ▸ linkedNodes
  have linkedCodesNext : WitnessArrayLinked next si 56 64 codeArray codeCount input inputLength firstHeap :=
    readyEq ▸ linkedCodes
  have liveNext : ∀ address : BitVec 64, firstHeap.toNat ≤ address.toNat →
      address.toNat < 33806089496 → next.memaddrs address := fun a lo hi => readyEq ▸ live a lo hi
  have context := validFacts.database_context (setVarHOLFinite (ofString "pl") (.val (.word payload)) s)
    validated si array count input inputLength scratch frame heap keccakState keccakPad parent ceiling
  obtain ⟨atSiNext,_,_,_,_,_,_,atStateNext,atPadNext,codeNext,_,_⟩ := context
  have entryCode : (setVarHOLFinite (ofString "pl") (.val (.word payload)) s).code = originalRuntimeCode :=
    code
  have scratchKeep : validated.globals.lookup (ofString "mpt_hash_scratch") =
      s.globals.lookup (ofString "mpt_hash_scratch") :=
    validFacts.mpt_hash_scratch (setVarHOLFinite (ofString "pl") (.val (.word payload)) s) validated si array
      count input inputLength scratch frame heap keccakState keccakPad ceiling entryCode
  have nextCode : next.code = originalRuntimeCode := codeNext.trans entryCode
  have outputNext : next.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)) := by
    have hashesN : (ofString "block_hashes_n" == ofString "mpt_hash_scratch") = false := by decide
    have hashes : (ofString "block_hashes" == ofString "mpt_hash_scratch") = false := by decide
    simp only [next,runAttemptDatabaseState,setGlobalHOLFinite,setVarHOLFinite,
      HolFiniteMapExact.lookup_update,FUPDATE,hashesN,hashes]
    exact scratchKeep.trans outputGlobal
  have step := run_attempt_two_database_values_input_reaches next si firstHeap nodeCount nodeArray codeCount codeArray
    input inputLength keccakState keccakPad output atSiNext linkedNodesNext linkedCodesNext nextCode atHNext
    alHeap bounded atStateNext atPadNext outputNext (by omega) outputAligned windows₁ windows₂
    (fun a _ lo hi => liveNext a lo hi) inputLimit inputBound inputCap (readyEq ▸ tailBudget) ceiling
    stateBelow padBelow outputBelow recordAbove (by omega) nodesAbove codesAbove
  refine readyEq.symm ▸ (reaches_mono next (runAttemptAt 9) (runAttemptAt 11) _ _ _ _ (Nat.le_refl _) ?_ step)
  intro final f
  obtain ⟨midHeap,finalHeap,localsFinal,domain,codeFinal,endian,stFinal,padFinal,outFinal,atFinal,
    firstBelow,midBelow,alFinal,capFinal,nodeValues,codeValues,nodeTable,codeTable,liveFinal,frameFinal⟩ := f
  exact ⟨next,validated,parent,firstHeap,midHeap,finalHeap,validFacts,nonempty,rfl,monotone,localsFinal,
    domain,codeFinal.trans codeNext,endian,stFinal,padFinal,outFinal,atFinal,firstBelow,midBelow,
    alFinal,capFinal,nodeValues,codeValues,nodeTable,codeTable,liveFinal,frameFinal⟩

#print axioms run_attempt_entry_to_two_database_values
end InitECandidate.Runtime
