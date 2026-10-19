import InitECandidate.Runtime.ValidateHeadersCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- The actual run_attempt header argument loads connect the decoder's real
linked witness to the installed validation-call runtime bound. -/
theorem runBounded_run_attempt_headers_call {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si array count input inputLength scratch frame heap keccakState keccakPad : BitVec 64) (ceiling inputLimit : Nat)
    (inputBound : inputLength.toNat ≤ inputLimit) (inputCap : inputLimit ≤ 134217712)
    (inputAfter : ceiling ≤ input.toNat) (tableAbove : ceiling ≤ array.toNat)
    (inputBefore : input.toNat + inputLength.toNat ≤ heap.toNat)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (ceilingAligned : ceiling % 8 = 0) (stateBelow : keccakState.toNat + 200 ≤ ceiling) (padBelow : keccakPad.toNat + 136 ≤ ceiling)
    (destination : Option (VarKind × MlS))
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
    RunBounded s (.call (some (destination,none)) (ofString "validate_headers") runAttemptHeadersArguments)
      (validateHeadersBodyCost inputLimit + 1) := by
  exact runBounded_validate_headers_call s array count input inputLength scratch frame heap keccakState keccakPad ceiling inputLimit
    inputBound inputCap inputAfter tableAbove linked.arrayEnd inputBefore orderedFrame framePositive scratchBelow ceilingAligned stateBelow padBelow
    destination runAttemptHeadersArguments (eval_run_attempt_headers_arguments s si array count input inputLength heap atSi linked)
    linked.slices scratchGlobal frameGlobal stateGlobal padGlobal arena heapArena heapGlobal heapBound code budget

#print axioms runBounded_run_attempt_headers_call
end InitECandidate.Runtime
