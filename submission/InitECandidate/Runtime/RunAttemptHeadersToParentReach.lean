import InitECandidate.Runtime.RunAttemptHeadersDeclarationPointerContract
import InitECandidate.Runtime.RunAttemptCountParentReach
import InitECandidate.Runtime.RunAttemptBlockHashesReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
/-- Retained actual validation evidence and caller facts, before the zero-cost
count/parent prefix; named so later compositions preserve every contract fact. -/
def RunAttemptHeaderValidationFacts {F : Type} (s ready : PanSemStateFiniteExact 64 F)
    (si array count input inputLength scratch frame heap keccakState keccakPad : BitVec 64) (ceiling : Nat) : Prop :=
∃ value : ValueHOL 64, ∃ bodyPost : PanSemStateFiniteExact 64 F,
        evaluateHOLFiniteState (callEntryStateHOLFinite s (validateHeadersCallee array count))
          (sourceFunctionBody Guest.guestFn_validate_headers) = (some (.returned value),bodyPost) ∧
        ready.locals = s.locals.update (ofString "vh",value) ∧
        ready.memory = bodyPost.memory ∧ ready.globals = bodyPost.globals ∧
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
        value = .rStruct [.val (.word heap),.val (.word (allocationEnd heap (validateHeadersHsSize count)))] ∧
        ready.locals.lookup (ofString "vh") =
          some (.rStruct [.val (.word heap),.val (.word (allocationEnd heap (validateHeadersHsSize count)))]) ∧
        count.toNat ≤ 256 ∧
        (∃ finalHeap : BitVec 64,
          ready.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
          heap.toNat ≤ finalHeap.toNat ∧ finalHeap.toNat ≤ 33806089496 ∧ finalHeap.toNat % 8 = 0 ∧
          (∀ address : BitVec 64, finalHeap.toNat ≤ address.toNat → address.toNat < 33806089496 →
            bodyPost.memaddrs address) ∧
          (∀ address : BitVec 64, finalHeap.toNat ≤ address.toNat → address.toNat < 33806089496 →
            ready.memaddrs address)) ∧
        ready.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
        ready.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
        ready.globals.lookup (ofString "keccak_st") = some (.val (.word keccakState)) ∧
        ready.globals.lookup (ofString "keccak_pad") = some (.val (.word keccakPad)) ∧
        (∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < heap.toNat →
          ready.memory address = s.memory address) ∧
        RlpSliceInputPrefix bodyPost array input inputLength count.toNat ∧
        RlpSliceInputPrefix ready array input inputLength count.toNat ∧
        HeaderPointerPrefix ready heap count.toNat ∧
        ready.locals.lookup (ofString "si") = some (.val (.word si))

theorem run_attempt_headers_to_parent_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si array count input inputLength scratch frame heap keccakState keccakPad : BitVec 64)
    (ceiling inputLimit : Nat)
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
    Reaches s (runAttemptAt 2)
      (fun final => ∃ validated : PanSemStateFiniteExact 64 F, ∃ parent : BitVec 64,
        RunAttemptHeaderValidationFacts s validated si array count input inputLength scratch frame heap keccakState keccakPad ceiling ∧
        count ≠ 0 ∧ final = setVarHOLFinite (ofString "parent") (.val (.word parent))
          (setVarHOLFinite (ofString "nh") (.val (.word count)) validated))
      (validateHeadersBodyCost inputLimit + 1) (runAttemptAt 6) := by
  have checked := run_attempt_headers_declaration_pointer_contract s si array count input inputLength scratch frame heap
    keccakState keccakPad ceiling inputLimit inputBound inputCap inputAfter tableAbove inputBefore orderedFrame
    framePositive scratchBelow ceilingAligned stateBelow padBelow atSi linked scratchGlobal frameGlobal stateGlobal
    padGlobal arena heapArena heapGlobal heapBound code budget
  have combined := reaches_trans s (runAttemptAt 2) (runAttemptAt 3) (runAttemptAt 6)
    (fun ready => RunAttemptHeaderValidationFacts s ready si array count input inputLength scratch frame heap keccakState keccakPad ceiling)
    (fun final => ∃ validated : PanSemStateFiniteExact 64 F, ∃ parent : BitVec 64,
        RunAttemptHeaderValidationFacts s validated si array count input inputLength scratch frame heap keccakState keccakPad ceiling ∧
        count ≠ 0 ∧ final = setVarHOLFinite (ofString "parent") (.val (.word parent))
          (setVarHOLFinite (ofString "nh") (.val (.word count)) validated)) (validateHeadersBodyCost inputLimit + 1) 0 checked (by
      intro ready facts
      have retained := facts
      obtain ⟨value,bodyPost,bodyRun,locals,memoryEq,globalsEq,domainEq,codeEq,valueIs,vhLocal,countCap,frontier,
        scratchPost,framePost,statePost,padPost,windowPost,tablePost,prefixReady,initialized,atSiReady⟩ := facts
      have parentRun := run_attempt_count_parent_window_reaches s ready si array count input inputLength heap
        (allocationEnd heap (validateHeadersHsSize count)) ceiling linked atSiReady vhLocal domainEq
        recordAbove recordBefore windowPost initialized
      exact reaches_mono ready (runAttemptAt 3) (runAttemptAt 6) _ _ 0 0 (le_refl _)
        (fun final result => by
          obtain ⟨nonzero,parent,same⟩ := result
          exact ⟨ready,parent,retained,nonzero,same⟩) parentRun)
  simpa only [Nat.add_zero] using combined

#print axioms run_attempt_headers_to_parent_reaches
theorem run_attempt_headers_to_database_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si array count input inputLength scratch frame heap keccakState keccakPad : BitVec 64)
    (ceiling inputLimit : Nat)
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
    Reaches s (runAttemptAt 2)
      (fun final => ∃ validated : PanSemStateFiniteExact 64 F, ∃ parent : BitVec 64,
        RunAttemptHeaderValidationFacts s validated si array count input inputLength scratch frame heap keccakState keccakPad ceiling ∧
        count ≠ 0 ∧ final = setGlobalHOLFinite (ofString "block_hashes_n") (.val (.word count))
          (setGlobalHOLFinite (ofString "block_hashes") (.val (.word (allocationEnd heap (validateHeadersHsSize count))))
            (setVarHOLFinite (ofString "parent") (.val (.word parent))
              (setVarHOLFinite (ofString "nh") (.val (.word count)) validated))))
      (validateHeadersBodyCost inputLimit + 1) (runAttemptAt 9) := by
  have reached := run_attempt_headers_to_parent_reaches s si array count input inputLength scratch frame heap
    keccakState keccakPad ceiling inputLimit inputBound inputCap inputAfter tableAbove inputBefore orderedFrame
    framePositive scratchBelow ceilingAligned stateBelow padBelow atSi linked scratchGlobal frameGlobal stateGlobal
    padGlobal arena heapArena heapGlobal heapBound code recordAbove recordBefore budget
  have combined := reaches_trans s (runAttemptAt 2) (runAttemptAt 6) (runAttemptAt 9) _
    (fun final => ∃ validated : PanSemStateFiniteExact 64 F, ∃ parent : BitVec 64,
        RunAttemptHeaderValidationFacts s validated si array count input inputLength scratch frame heap keccakState keccakPad ceiling ∧
        count ≠ 0 ∧ final = setGlobalHOLFinite (ofString "block_hashes_n") (.val (.word count))
          (setGlobalHOLFinite (ofString "block_hashes") (.val (.word (allocationEnd heap (validateHeadersHsSize count))))
            (setVarHOLFinite (ofString "parent") (.val (.word parent))
              (setVarHOLFinite (ofString "nh") (.val (.word count)) validated)))) (validateHeadersBodyCost inputLimit + 1) 0 reached (by
      intro next facts
      obtain ⟨validated,parent,kept,nonzero,same⟩ := facts
      subst next
      have original := kept
      obtain ⟨value,bodyPost,bodyRun,locals,memoryEq,globalsEq,domainEq,codeEq,valueIs,vhLocal,rest⟩ := kept
      have vh : (setVarHOLFinite (ofString "parent") (.val (.word parent))
          (setVarHOLFinite (ofString "nh") (.val (.word count)) validated)).locals.lookup (ofString "vh") =
          some (.rStruct [.val (.word heap),.val (.word (allocationEnd heap (validateHeadersHsSize count)))]) := by
        simpa (config := {decide := true}) [setVarHOLFinite,FUPDATE] using vhLocal
      have nh : (setVarHOLFinite (ofString "parent") (.val (.word parent))
          (setVarHOLFinite (ofString "nh") (.val (.word count)) validated)).locals.lookup (ofString "nh") =
          some (.val (.word count)) := by
        simp (config := {decide := true}) [setVarHOLFinite,FUPDATE]
      have assigned := run_attempt_block_hashes_reaches _ heap
        (allocationEnd heap (validateHeadersHsSize count)) count vh nh
      exact reaches_mono _ (runAttemptAt 6) (runAttemptAt 9) _ _ 0 0 (le_refl _)
        (fun final same => ⟨validated,parent,original,nonzero,same⟩) assigned)
  simpa only [Nat.add_zero] using combined

#print axioms run_attempt_headers_to_database_reaches
end InitECandidate.Runtime
