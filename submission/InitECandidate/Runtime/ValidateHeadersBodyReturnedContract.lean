import InitECandidate.Runtime.ValidateHeadersBodyBound
import InitECandidate.Runtime.ValidateHeadersSecondPhaseFrame
import InitECandidate.Runtime.ReachesReturnedContinuation
import InitECandidate.Runtime.ValidateHeadersThroughFirstWindowWorkspaceReach
/-!
The complete original header-validation body, on an actual returned outcome,
delivers the validated header count, the original `(hs, hashes)` buffer pair,
a monotone aligned bounded allocation frontier with its live arena, the
untouched caller workspace pointers, the untouched `[ceiling, hs)` record
window, the original witness prefix and unmodified code.

Everything is derived from root's checked window/workspace first-phase reach
(`validate_headers_through_first_window_workspace_reaches`), the
returned-continuation transfer of the reach layer
(`reaches_returned_continuation`) and the checked `At 5` second-phase
frame/returned pair (`evaluate_validate_headers_second_phase_returned`).
No callee contract is assumed.
-/
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- Every actual returned run of the original header-validation body reports
the true header count, the `(hs, hashes)` pair built from the entry allocation
frontier, a monotone and 8-aligned dynamic frontier below `HEAPEND` together
with its live arena, the caller workspace pointers, the untouched older
memory window, the original input witness prefix and unmodified code. -/
theorem validate_headers_body_returned_contract {F : Type} (s post : PanSemStateFiniteExact 64 F)
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
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode)
    (budget : validateHeadersBodyCost inputLimit ≤ s.clock)
    (v : ValueHOL 64)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_validate_headers) =
      (some (.returned v),post)) :
    count.toNat ≤ 256 ∧
    (∃ finalHeap : BitVec 64,
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
      heap.toNat ≤ finalHeap.toNat ∧ finalHeap.toNat ≤ 33806089496 ∧ finalHeap.toNat % 8 = 0 ∧
      (∀ address : BitVec 64, finalHeap.toNat ≤ address.toNat → address.toNat < 33806089496 →
        post.memaddrs address)) ∧
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
    post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
    post.globals.lookup (ofString "keccak_st") = some (.val (.word keccakState)) ∧
    post.globals.lookup (ofString "keccak_pad") = some (.val (.word keccakPad)) ∧
    (∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < heap.toNat →
      post.memory address = s.memory address) ∧
    RlpSliceInputPrefix post array input inputLength count.toNat ∧
    post.code = s.code ∧
    v = .rStruct [.val (.word heap),.val (.word (allocationEnd heap (validateHeadersHsSize count)))] := by
  have bodyRun : evaluateHOLFiniteState s (validateHeadersAt 0) = (some (.returned v),post) := by
    rw [← source_validate_headers_body]
    exact run
  have reached := validate_headers_through_first_window_workspace_reaches s array count input inputLength
    scratch frame heap keccakState keccakPad ceiling inputLimit inputBound inputCap inputAfter tableAbove
    tableBefore inputBefore orderedFrame framePositive scratchBelow ceilingAligned stateBelow padBelow atArray
    atCount table scratchGlobal frameGlobal stateGlobal padGlobal arena heapArena heapGlobal heapBound code
    (by have small := budget; simp only [validateHeadersBodyCost] at small; omega)
  obtain ⟨next,evidence,spent,remaining,agreement,tailRun⟩ :=
    reaches_returned_continuation s (validateHeadersAt 0) (validateHeadersAt 5) _ _ v reached
      (by rw [bodyRun])
  obtain ⟨e,arrayEq,countEq,inputEq,lengthEq,limitEq,hsEq,hashEq,windowInvariant,installed,ceilingEq,
    scratchEq,frameEq,stateEq,padEq⟩ := evidence
  obtain ⟨aligned,window⟩ := windowInvariant
  obtain ⟨⟨index,frontier,atArrNext,atNNext,atINext,atHsNext,atHashesNext,within,distance,tableNext,
    belowInput,belowTable,gScratch,gFrame,gHeap,gState,gPad,frontierBound,frameArena,frontierArena⟩,
    finalHeap,gHeapFinal,lowerBound,alignedFinal⟩ := aligned
  have finalHeapEq : finalHeap = frontier := by
    have wordEq := gHeapFinal.symm.trans gHeap
    simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at wordEq
    exact wordEq
  have lowerFrontier : heap.toNat ≤ frontier.toNat := by
    rw [hsEq,finalHeapEq] at lowerBound
    exact lowerBound
  have alignedFrontier : frontier.toNat % 8 = 0 := by
    rw [← finalHeapEq]
    exact alignedFinal
  have tailPair : evaluateHOLFiniteState next (validateHeadersSecondAt 5) =
      (some (.returned v),(evaluateHOLFiniteState next (validateHeadersAt 5)).2) := Prod.ext tailRun rfl
  have phaseReturned := evaluate_validate_headers_second_phase_returned next heap
    (allocationEnd heap (validateHeadersHsSize count)) v _ (installed.trans code)
    (by rw [← hsEq]; exact atHsNext) (by rw [← hashEq]; exact atHashesNext) tailPair
  obtain ⟨valueEq,phaseMemory,phaseGlobals,phaseDomain,phaseBe,phaseCode⟩ := phaseReturned
  rw [bodyRun] at agreement
  have memoryEq : post.memory = next.memory := agreement.2.2.1.trans phaseMemory
  have globalsEq : post.globals = next.globals := agreement.2.2.2.1.trans phaseGlobals
  have domainEq : post.memaddrs = next.memaddrs := agreement.2.2.2.2.trans phaseDomain
  have metadata := evaluateHOLFiniteState_metadata s (validateHeadersAt 0)
  rw [bodyRun] at metadata
  have tableFinal : RlpSliceInputPrefix next array input inputLength count.toNat := by
    rw [← arrayEq,← countEq,← inputEq,← lengthEq]
    exact tableNext
  have tablePost : RlpSliceInputPrefix post array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨pointer,length,entry⟩ := tableFinal slot inside
    exact ⟨pointer,length,RlpSliceInputEntry.after_frame next post array slot pointer length input inputLength entry
      (by rw [domainEq]) (by rw [memoryEq]) (by rw [memoryEq])⟩
  have scratchPost : post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) := by
    rw [globalsEq]
    rw [← scratchEq]
    exact gScratch
  have framePost : post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
    rw [globalsEq]
    rw [← frameEq]
    exact gFrame
  have statePost : post.globals.lookup (ofString "keccak_st") = some (.val (.word keccakState)) := by
    rw [globalsEq]
    rw [← stateEq]
    exact gState
  have padPost : post.globals.lookup (ofString "keccak_pad") = some (.val (.word keccakPad)) := by
    rw [globalsEq]
    rw [← padEq]
    exact gPad
  have windowPost : ∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < heap.toNat →
      post.memory address = s.memory address := by
    intro address low high
    rw [memoryEq]
    exact window address (by rw [ceilingEq]; exact low) (by rw [hsEq]; exact high)
  exact ⟨by rw [← countEq]; exact e.cap,
    ⟨frontier,(by rw [globalsEq]; exact gHeap),lowerFrontier,frontierBound,alignedFrontier,
      (by intro address lo hi; rw [domainEq]; exact frontierArena address lo hi)⟩,
    scratchPost,framePost,statePost,padPost,windowPost,tablePost,metadata.1,valueEq⟩

#print axioms validate_headers_body_returned_contract
end InitECandidate.Runtime
