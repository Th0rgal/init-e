import InitECandidate.Runtime.RunAttemptHeadersCallBound
import InitECandidate.Runtime.BoundedDecCallReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- The actual run_attempt declaration reaches its actual continuation with
an execution-derived validation result, or terminates within the proved
callee budget. The returned body run is retained for stronger contracts. -/
theorem run_attempt_headers_declaration_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si array count input inputLength scratch frame heap keccakState keccakPad : BitVec 64) (ceiling inputLimit : Nat)
    (inputBound : inputLength.toNat ≤ inputLimit) (inputCap : inputLimit ≤ 134217712)
    (inputAfter : ceiling ≤ input.toNat) (tableAbove : ceiling ≤ array.toNat)
    (inputBefore : input.toNat + inputLength.toNat ≤ heap.toNat)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (ceilingAligned : ceiling % 8 = 0) (stateBelow : keccakState.toNat + 200 ≤ ceiling) (padBelow : keccakPad.toNat + 136 ≤ ceiling)
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
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code)
      (validateHeadersBodyCost inputLimit + 1) (runAttemptAt 3) := by
  have args := eval_run_attempt_headers_arguments s si array count input inputLength heap atSi linked
  have lookup : lookupCodeHOLFinite s.code.lookup (ofString "validate_headers")
      [.val (.word array),.val (.word count)] =
      some (sourceFunctionBody Guest.guestFn_validate_headers,validateHeadersCallee array count,.comb [.one,.one]) := by
    rw [code]
    exact lookup_validate_headers_callee array count
  let entry := callEntryStateHOLFinite s (validateHeadersCallee array count)
  obtain ⟨atArray,atCount,table,arrayEnd,countBound⟩ := run_attempt_headers_entry s si array count input inputLength heap linked
  have bounded := runBounded_validate_headers_body entry array count input inputLength scratch frame heap keccakState keccakPad ceiling inputLimit
    inputBound inputCap inputAfter tableAbove arrayEnd inputBefore orderedFrame framePositive scratchBelow ceilingAligned stateBelow padBelow
    atArray atCount table scratchGlobal frameGlobal stateGlobal padGlobal arena heapArena heapGlobal heapBound code
    (by change validateHeadersBodyCost inputLimit ≤ s.clock - 1; omega)
  rw [source_run_attempt_headers_call]
  apply bounded_decCall_reaches s (ofString "vh") (ofString "validate_headers") (.comb [.one,.one]) (.comb [.one,.one])
    runAttemptHeadersArguments [.val (.word array),.val (.word count)] (sourceFunctionBody Guest.guestFn_validate_headers)
    (runAttemptAt 3) (validateHeadersCallee array count) (validateHeadersBodyCost inputLimit) _ args lookup budget bounded
  intro value bodyPost bodyRun checked
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_validate_headers)
  rw [bodyRun] at metadata
  exact ⟨value,bodyPost,bodyRun,rfl,rfl,rfl,metadata.2.1,metadata.1⟩

#print axioms run_attempt_headers_declaration_reaches
end InitECandidate.Runtime
