import InitECandidate.Runtime.ValidateHeadersBodyBound
import InitECandidate.Runtime.ValidateHeadersSecondPhaseFrame
import InitECandidate.Runtime.ReachesReturnedContinuation
import InitECandidate.Runtime.WorkspaceGlobalsKeep
/-!
The complete original header-validation body, on an actual returned outcome,
delivers the validated header count, the original `(hs, hashes)` buffer pair,
a bounded dynamic allocation frontier, the untouched parser workspace
pointers, the original witness prefix and the unmodified code.

Everything is derived from root's checked first-phase reach
(`validate_headers_through_first_phase_reaches`), the returned-continuation
transfer of the reach layer (`reaches_returned_continuation`) and the checked
`At 5` second-phase frame/returned pair. No callee contract is assumed.
-/
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000000
set_option cbv.warning false

/-! ### Workspace pointers survive the original validation body -/

/-- The actual validation body keeps every parser workspace global. -/
theorem validate_headers_keeps_parser_workspace {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (member : name ∈ parserWorkspaceGlobals) (code : s.code = originalRuntimeCode) :
    (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_validate_headers)).2.globals.lookup name =
      s.globals.lookup name :=
  evaluate_keeps_parser_workspace name member _
    (parser_workspace_installed originalRuntimeCode_validateHeaders_lookup (by decide) name member) s code

/-! ### Returned contract of the whole original body -/

/-- The real first phase reached with its environment pinned at the entry
workspace words: the two allocations, the index initialization and the whole
first loop land on the `At 5` continuation with an exhausted invariant whose
scratch, frame and Keccak environment components are the entry values. -/
theorem validate_headers_environment_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
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
    (budget : 4 + validateHeadersFirstLoopCost inputLimit ≤ s.clock) :
    Reaches s (validateHeadersAt 0)
      (fun post => ∃ e : ValidateHeadersFirstEnvironment,
        e.array = array ∧ e.count = count ∧ e.input = input ∧ e.inputLength = inputLength ∧
        e.inputLimit = inputLimit ∧ e.scratch = scratch ∧ e.frame = frame ∧
        e.keccakState = keccakState ∧ e.keccakPad = keccakPad ∧
        e.hs = heap ∧ e.hashes = allocationEnd heap (validateHeadersHsSize count) ∧
        ValidateHeadersFirstInvariant e post 0 ∧ post.code = s.code)
      (4 + validateHeadersFirstLoopCost inputLimit) (validateHeadersAt 5) := by
  have allocated := validate_headers_prefix_reaches s count heap code atCount heapGlobal heapBound (by omega)
  apply reaches_trans_budget s (validateHeadersAt 0) (validateHeadersAt 3) (validateHeadersAt 5) _ _
    4 (validateHeadersFirstLoopCost inputLimit) budget allocated
  intro ready facts remaining
  obtain ⟨cap,first,hsAllocation,hashAllocation⟩ := facts
  obtain ⟨hs,hashes,n,heapGlobalReady,memory,domain,installed,hsExtent,hashExtent,hashAligned,heapAligned,
    heapBoundReady,globals⟩ :=
    validate_headers_buffers s first ready count heap cap atCount hsAllocation hashAllocation
  let e : ValidateHeadersFirstEnvironment := {
    array := array, count := count, input := input, inputLength := inputLength,
    scratch := scratch, frame := frame, hs := heap, hashes := allocationEnd heap (validateHeadersHsSize count),
    keccakState := keccakState, keccakPad := keccakPad, ceiling := ceiling, inputLimit := inputLimit,
    cap := cap, inputBound := inputBound, inputCap := inputCap, inputAfter := inputAfter, tableAbove := tableAbove,
    tableBeforeHs := tableBefore, hsBufferBound := by omega, hashBufferBound := by omega,
    hashAligned := hashAligned, hsBeforeHashes := by omega, orderedFrame := orderedFrame,
    framePositive := framePositive, scratchBelow := scratchBelow, ceilingAligned := ceilingAligned,
    stateBelow := stateBelow, padBelow := padBelow }
  obtain ⟨prepared,installedCode⟩ := validate_headers_allocated_ready e s first ready atArray atCount table
    inputBefore scratchGlobal frameGlobal stateGlobal padGlobal arena heapArena rfl hsAllocation hashAllocation
  have phase := validate_headers_first_phase_reaches e ready (installedCode.trans code) prepared (by omega)
  exact reaches_mono ready (validateHeadersAt 3) (validateHeadersAt 5) _ _ _ _ (le_refl _)
    (fun post result =>
      ⟨e,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,result.1,result.2.trans installedCode⟩) phase

/-- Every actual returned run of the original header-validation body reports
the true header count, the `(hs, hashes)` pair built from the entry allocation
frontier, a bounded dynamic frontier with its live arena, the untouched
parser workspace and scratch pointers, the original input witness prefix and
unmodified code. -/
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
      finalHeap.toNat ≤ 33806089496 ∧
      (∀ address : BitVec 64, finalHeap.toNat ≤ address.toNat → address.toNat < 33806089496 →
        post.memaddrs address)) ∧
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
    post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
    post.globals.lookup (ofString "keccak_st") = some (.val (.word keccakState)) ∧
    post.globals.lookup (ofString "keccak_pad") = some (.val (.word keccakPad)) ∧
    RlpSliceInputPrefix post array input inputLength count.toNat ∧
    post.code = s.code ∧
    v = .rStruct [.val (.word heap),.val (.word (allocationEnd heap (validateHeadersHsSize count)))] := by
  have bodyRun : evaluateHOLFiniteState s (validateHeadersAt 0) = (some (.returned v),post) := by
    rw [← source_validate_headers_body]
    exact run
  have reached := validate_headers_environment_reaches s array count input inputLength scratch frame
    heap keccakState keccakPad ceiling inputLimit inputBound inputCap inputAfter tableAbove tableBefore inputBefore
    orderedFrame framePositive scratchBelow ceilingAligned stateBelow padBelow atArray atCount table scratchGlobal
    frameGlobal stateGlobal padGlobal arena heapArena heapGlobal heapBound code
    (by have small := budget; simp only [validateHeadersBodyCost] at small; omega)
  obtain ⟨next,evidence,spent,remaining,agreement,tailRun⟩ :=
    reaches_returned_continuation s (validateHeadersAt 0) (validateHeadersAt 5) _ _ v reached
      (by rw [bodyRun])
  obtain ⟨e,arrayEq,countEq,inputEq,lengthEq,limitEq,scratchEq,frameEq,stateEq,padEq,hsEq,hashEq,invariant,
    installed⟩ := evidence
  obtain ⟨index,frontier,atArrNext,atNNext,atINext,atHsNext,atHashesNext,within,distance,tableNext,
    belowInput,belowTable,gScratch,gFrame,gHeap,gState,gPad,frontierBound,frameArena,frontierArena⟩ := invariant
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
    rw [← scratchEq]; rw [globalsEq]; exact gScratch
  have framePost : post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
    rw [← frameEq]; rw [globalsEq]; exact gFrame
  have statePost : post.globals.lookup (ofString "keccak_st") = some (.val (.word keccakState)) := by
    rw [← stateEq]; rw [globalsEq]; exact gState
  have padPost : post.globals.lookup (ofString "keccak_pad") = some (.val (.word keccakPad)) := by
    rw [← padEq]; rw [globalsEq]; exact gPad
  exact ⟨by rw [← countEq]; exact e.cap,
    ⟨frontier,(by rw [globalsEq]; exact gHeap),frontierBound,
      (by intro address low high; rw [domainEq]; exact frontierArena address low high)⟩,
    scratchPost,framePost,statePost,padPost,tablePost,metadata.1,valueEq⟩

/-- Pinning the environment fields at the entry workspace words turns the
reached scratch pointers into their entry values. -/
theorem scratch_frame_entry_of_environment {F : Type} (post : PanSemStateFiniteExact 64 F)
    (e : ValidateHeadersFirstEnvironment) (scratch frame : BitVec 64)
    (atScratch : post.globals.lookup (ofString "scratch_ptr") = some (.val (.word e.scratch)))
    (atFrame : post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word e.frame)))
    (environmentScratch : e.scratch = scratch) (environmentFrame : e.frame = frame) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) :=
  ⟨by rw [← environmentScratch]; exact atScratch, by rw [← environmentFrame]; exact atFrame⟩

#print axioms validate_headers_body_returned_contract
#print axioms scratch_frame_entry_of_environment
#print axioms validate_headers_keeps_parser_workspace
#print axioms validate_headers_environment_reaches
end InitECandidate.Runtime
