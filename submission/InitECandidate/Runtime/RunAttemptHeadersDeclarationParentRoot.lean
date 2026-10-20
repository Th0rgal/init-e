import InitECandidate.Runtime.RunAttemptHeadersToParentReach
import InitECandidate.Runtime.ValidateHeadersBodyReturnedParentRoot
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def SelectedHeaderRoot {F : Type} (state : PanSemStateFiniteExact 64 F)
    (headers hashes count : BitVec 64) : Prop :=
  ∃ heap header root : BitVec 64,
    state.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
    state.memory (headers+(count-1)*8)=.word header ∧
    state.memory (header+32#64)=.word root ∧ state.memaddrs (header+32#64) ∧
    header.toNat+248≤heap.toNat ∧ hashes.toNat+count.toNat*32+32≤header.toNat

/-- The actual caller declaration retains the original complete metadata and
supplies the selected state root whenever its later nonempty guard succeeds. -/
theorem run_attempt_headers_declaration_parent_root {F : Type} (s : PanSemStateFiniteExact 64 F)
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
    (heapUpper : heap.toNat≤33805910000)
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode)
    (budget : validateHeadersBodyCost inputLimit + 1 ≤ s.clock) :
    Reaches s (runAttemptAt 2)
      (fun ready => RunAttemptHeaderValidationFacts s ready si array count input inputLength
        scratch frame heap keccakState keccakPad ceiling ∧
        (count≠0→SelectedHeaderRoot ready heap (allocationEnd heap (validateHeadersHsSize count)) count))
      (validateHeadersBodyCost inputLimit+1) (runAttemptAt 3) := by
  have reached := run_attempt_headers_declaration_pointer_contract s si array count input inputLength scratch frame heap
    keccakState keccakPad ceiling inputLimit inputBound inputCap inputAfter tableAbove inputBefore orderedFrame
    framePositive scratchBelow ceilingAligned stateBelow padBelow atSi linked scratchGlobal frameGlobal
    stateGlobal padGlobal arena heapArena heapGlobal heapBound code budget
  apply reaches_mono s (runAttemptAt 2) (runAttemptAt 3) _ _ _ _ (Nat.le_refl _) _ reached
  intro ready facts
  refine ⟨facts,?_⟩
  intro nonzero
  obtain ⟨value,bodyPost,bodyRun,_,memoryEq,globalsEq,domainEq,rest⟩ := facts
  obtain ⟨atArray,atCount,table,arrayEnd,_⟩ :=
    run_attempt_headers_entry s si array count input inputLength heap linked
  let entry := callEntryStateHOLFinite s (validateHeadersCallee array count)
  obtain ⟨_,liveHeap,header,root,binding,cell,rootCell,domain,extent,floor⟩ :=
    validate_headers_body_returned_parent_root entry bodyPost array count input inputLength scratch frame heap
      keccakState keccakPad ceiling inputLimit inputBound inputCap inputAfter tableAbove arrayEnd inputBefore
      orderedFrame framePositive scratchBelow ceilingAligned stateBelow padBelow atArray atCount table
      scratchGlobal frameGlobal stateGlobal padGlobal arena heapArena heapGlobal heapUpper nonzero heapBound code
      (by change validateHeadersBodyCost inputLimit≤s.clock-1; omega) value bodyRun
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_validate_headers)
  rw [bodyRun] at metadata
  have addresses : ready.memaddrs=bodyPost.memaddrs := domainEq.trans metadata.2.1.symm
  refine ⟨liveHeap,header,root,?_,?_,?_,?_,extent,floor⟩
  · rw [globalsEq]; exact binding
  · rw [memoryEq]; exact cell
  · rw [memoryEq]; exact rootCell
  · rw [addresses]; exact domain

#print axioms run_attempt_headers_declaration_parent_root
end InitECandidate.Runtime
