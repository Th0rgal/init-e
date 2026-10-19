import InitECandidate.Runtime.RunAttemptHeadersDeclarationContract
import InitECandidate.Runtime.ValidateHeadersBodyReturnedPointerPrefix
/-!
The actual `run_attempt` header-validation declaration, carrying the returned
header-pointer prefix through the real caller.

Root's `validate_headers_body_returned_pointer_prefix` proves that every returned
original validating run leaves the complete readable header-pointer buffer at
the caller's `heap`.  This module applies it to the returned body run retained by
the actual declaration reach, transports the prefix to the reached
`runAttemptAt 3` state through the caller's retained memory and the evaluator
domain invariant, and keeps every fact of the existing declaration contract
(typed `vh` exact `(hs, hashes)` pair, the header count cap, the monotone aligned
frontier, the caller workspace pointers, the untouched older record window and
the retained witness prefix), plus the typed retained `si` local.  The reach is
strengthened in place at the same cost, with no new caller premise and no assumed
buffer fact.
-/
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- The actual `run_attempt` declaration reaches its real continuation while
carrying the returned contract of the original validating callee together with
the complete readable header-pointer buffer at the caller's heap. -/
theorem run_attempt_headers_declaration_pointer_contract {F : Type} (s : PanSemStateFiniteExact 64 F)
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
    (budget : validateHeadersBodyCost inputLimit + 1 ≤ s.clock) :
    Reaches s (runAttemptAt 2)
      (fun ready => ∃ value : ValueHOL 64, ∃ bodyPost : PanSemStateFiniteExact 64 F,
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
        ready.locals.lookup (ofString "si") = some (.val (.word si)))
      (validateHeadersBodyCost inputLimit + 1) (runAttemptAt 3) := by
  have reached := run_attempt_headers_declaration_contract s si array count input inputLength scratch frame heap
    keccakState keccakPad ceiling inputLimit inputBound inputCap inputAfter tableAbove inputBefore orderedFrame
    framePositive scratchBelow ceilingAligned stateBelow padBelow atSi linked scratchGlobal frameGlobal
    stateGlobal padGlobal arena heapArena heapGlobal heapBound code budget
  refine reaches_mono s (runAttemptAt 2) (runAttemptAt 3) _ _ _ _ (le_refl _) ?_ reached
  intro ready facts
  obtain ⟨value,bodyPost,bodyRun,pinLocal,memoryEq,globalsEq,domainEq,codeEq,valueIs,vhLocal,countCap,
    ⟨finalHeap,atFrontier,frontierLower,frontierBound,frontierAligned,frontierArena,frontierReady⟩,
    scratchPost,framePost,statePost,padPost,windowPost,tablePost,prefixReady⟩ := facts
  obtain ⟨atArray,atCount,table,arrayEnd,_countBound⟩ :=
    run_attempt_headers_entry s si array count input inputLength heap linked
  have pointerPrefix := validate_headers_body_returned_pointer_prefix
    (callEntryStateHOLFinite s (validateHeadersCallee array count)) bodyPost value array count input inputLength
    scratch frame heap keccakState keccakPad ceiling inputLimit inputBound inputCap inputAfter tableAbove arrayEnd
    inputBefore orderedFrame framePositive scratchBelow ceilingAligned stateBelow padBelow atArray atCount table
    scratchGlobal frameGlobal stateGlobal padGlobal arena heapArena heapGlobal heapBound code
    (by change validateHeadersBodyCost inputLimit ≤ s.clock - 1; omega) bodyRun
  have bodyMetadata := evaluateHOLFiniteState_metadata
    (callEntryStateHOLFinite s (validateHeadersCallee array count))
    (sourceFunctionBody Guest.guestFn_validate_headers)
  rw [bodyRun] at bodyMetadata
  have readyDomain : ready.memaddrs = bodyPost.memaddrs := domainEq.trans bodyMetadata.2.1.symm
  have readyPrefix : HeaderPointerPrefix ready heap count.toNat :=
    HeaderPointerPrefix.after_frame bodyPost ready heap count.toNat pointerPrefix readyDomain
      (fun slot _ => congrFun memoryEq (heap + slot * (8#64)))
  have atSiReady : ready.locals.lookup (ofString "si") = some (.val (.word si)) := by
    rw [pinLocal]
    simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
    exact atSi
  exact ⟨value,bodyPost,bodyRun,pinLocal,memoryEq,globalsEq,domainEq,codeEq,valueIs,vhLocal,countCap,
    ⟨finalHeap,atFrontier,frontierLower,frontierBound,frontierAligned,frontierArena,frontierReady⟩,
    scratchPost,framePost,statePost,padPost,windowPost,tablePost,prefixReady,readyPrefix,atSiReady⟩

#print axioms run_attempt_headers_declaration_pointer_contract
end InitECandidate.Runtime
