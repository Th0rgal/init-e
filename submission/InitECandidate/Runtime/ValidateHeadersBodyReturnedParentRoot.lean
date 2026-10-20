import InitECandidate.Runtime.ValidateHeadersThroughFirstRoomedWorkspaceReach
import InitECandidate.Runtime.ValidateHeadersRoomedExitLocals
import InitECandidate.Runtime.ValidateHeadersStoredRootsFinalParent
import InitECandidate.Runtime.ValidateHeadersBodyReturnedContract
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The complete actual header function returns its own buffers and retains
its last decoded header and state root below the actual live heap. -/
theorem validate_headers_body_returned_parent_root {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame heap keccakState keccakPad : BitVec 64) (ceiling inputLimit : Nat)
    (inputBound : inputLength.toNat ≤ inputLimit) (inputCap : inputLimit ≤ 134217712)
    (inputAfter : ceiling ≤ input.toNat) (tableAbove : ceiling ≤ array.toNat)
    (tableBefore : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (inputBefore : input.toNat + inputLength.toNat ≤ heap.toNat)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (ceilingAligned : ceiling % 8 = 0) (stateBelow : keccakState.toNat + 200 ≤ ceiling)
    (padBelow : keccakPad.toNat + 136 ≤ ceiling)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atCount : s.locals.lookup (ofString "n") = some (.val (.word count)))
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (stateGlobal : s.globals.lookup (ofString "keccak_st") = some (.val (.word keccakState)))
    (padGlobal : s.globals.lookup (ofString "keccak_pad") = some (.val (.word keccakPad)))
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (heapArena : ∀ address : BitVec 64, heap.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (heapGlobal : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapUpper : heap.toNat≤33805910000) (countNonzero : count≠0)
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode)
    (budget : validateHeadersBodyCost inputLimit ≤ s.clock)
    (v : ValueHOL 64)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_validate_headers) =
      (some (.returned v),post)) :
    v = .rStruct [.val (.word heap),.val (.word (allocationEnd heap (validateHeadersHsSize count)))] ∧
    ∃ liveHeap header root : BitVec 64,
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word liveHeap)) ∧
      post.memory (heap+(count-1)*8)=.word header ∧
      post.memory (header+32#64)=.word root ∧ post.memaddrs (header+32#64) ∧
      header.toNat+248≤liveHeap.toNat ∧
      (allocationEnd heap (validateHeadersHsSize count)).toNat+count.toNat*32+32≤header.toNat := by
  have bodyRun : evaluateHOLFiniteState s (validateHeadersAt 0)=(some (.returned v),post) := by
    rw [←source_validate_headers_body]
    exact run
  have reached := validate_headers_through_first_roomed_workspace_reaches s array count input inputLength
    scratch frame heap keccakState keccakPad ceiling inputLimit inputBound inputCap inputAfter tableAbove
    tableBefore inputBefore orderedFrame framePositive scratchBelow ceilingAligned stateBelow padBelow atArray
    atCount table scratchGlobal frameGlobal stateGlobal padGlobal arena heapArena heapGlobal heapUpper heapBound code
    (by have small := budget; simp only [validateHeadersBodyCost] at small; omega)
  obtain ⟨next,evidence,_,_,agreement,tailRun⟩ := reaches_returned_continuation s
    (validateHeadersAt 0) (validateHeadersAt 5) _ _ v reached (by rw [bodyRun])
  obtain ⟨e,arrayEq,countEq,inputEq,lengthEq,limitEq,hsEq,hashEq,roomed,installed,rest⟩ := evidence
  have locals := validate_headers_roomed_exit_locals e next roomed
  have tailPair : evaluateHOLFiniteState next (validateHeadersSecondAt 5)=
      (some (.returned v),(evaluateHOLFiniteState next (validateHeadersAt 5)).2) := Prod.ext tailRun rfl
  obtain ⟨pair,phaseMemory,phaseGlobals,phaseDomain,_,_⟩ :=
    evaluate_validate_headers_second_phase_returned next e.hs e.hashes v _
      (installed.trans code) locals.1 locals.2 tailPair
  obtain ⟨liveHeap,header,root,binding,cell,rootCell,domain,extent,floor⟩ :=
    validate_headers_stored_roots_parent_exhausted e next roomed.1 (by rw [countEq]; exact countNonzero)
  rw [bodyRun] at agreement
  have memoryEq : post.memory=next.memory := agreement.2.2.1.trans phaseMemory
  have globalsEq : post.globals=next.globals := agreement.2.2.2.1.trans phaseGlobals
  have domainEq : post.memaddrs=next.memaddrs := agreement.2.2.2.2.trans phaseDomain
  refine ⟨?_,liveHeap,header,root,?_,?_,?_,?_,extent,?_⟩
  · simpa only [hsEq,hashEq] using pair
  · rw [globalsEq]; exact binding
  · rw [memoryEq]; simpa only [hsEq,countEq] using cell
  · rw [memoryEq]; exact rootCell
  · rw [domainEq]; exact domain
  · simpa only [hashEq,countEq] using floor

#print axioms validate_headers_body_returned_parent_root
end InitECandidate.Runtime
