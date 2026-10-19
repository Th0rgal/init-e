import InitECandidate.Runtime.ValidateHeadersBodyBound
import InitECandidate.Runtime.ValidateHeadersThroughFirstPointerWorkspaceReach
import InitECandidate.Runtime.ValidateHeadersSecondPhaseFrame
import InitECandidate.Runtime.ReachesReturnedContinuation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- Every returned original validation run supplies the complete readable
header-pointer buffer, derived from its actual allocations and loop stores. -/
theorem validate_headers_body_returned_pointer_prefix {F : Type} (s post : PanSemStateFiniteExact 64 F) (value : ValueHOL 64)
    (array count input inputLength scratch frame heap keccakState keccakPad : BitVec 64) (ceiling inputLimit : Nat)
    (inputBound : inputLength.toNat ≤ inputLimit) (inputCap : inputLimit ≤ 134217712)
    (inputAfter : ceiling ≤ input.toNat) (tableAbove : ceiling ≤ array.toNat)
    (tableBefore : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (inputBefore : input.toNat + inputLength.toNat ≤ heap.toNat)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (ceilingAligned : ceiling % 8 = 0) (stateBelow : keccakState.toNat + 200 ≤ ceiling) (padBelow : keccakPad.toNat + 136 ≤ ceiling)
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
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_validate_headers) = (some (.returned value),post)) :
    HeaderPointerPrefix post heap count.toNat := by
  have firstPhase := validate_headers_through_first_pointer_workspace_reaches s array count input inputLength scratch frame heap keccakState keccakPad ceiling inputLimit
    inputBound inputCap inputAfter tableAbove tableBefore inputBefore orderedFrame framePositive scratchBelow ceilingAligned stateBelow padBelow
    atArray atCount table scratchGlobal frameGlobal stateGlobal padGlobal arena heapArena heapGlobal heapBound code
    (by unfold validateHeadersBodyCost at budget; omega)
  rw [source_validate_headers_body] at run
  obtain ⟨ready,facts,spent,remaining,agreement,returned⟩ := reaches_returned_continuation s (validateHeadersAt 0) (validateHeadersAt 5) _
    (4 + validateHeadersFirstLoopCost inputLimit) value firstPhase (by rw [run])
  obtain ⟨e,arrayEq,countEq,inputEq,lengthEq,limitEq,hsEq,hashEq,invariant,installed,ceilingEq,scratchEq,frameEq,stateEq,padEq⟩ := facts
  have frame := evaluate_validate_headers_second_phase_frame ready (installed.trans code)
  have memoryEq : post.memory = ready.memory := by
    rw [run] at agreement
    exact agreement.2.2.1.trans frame.1
  have domainEq : post.memaddrs = ready.memaddrs := by
    rw [run] at agreement
    exact agreement.2.2.2.2.trans frame.2.2.1
  have complete := validate_headers_first_pointer_prefix_exhausted e ready invariant
  have callerPrefix : HeaderPointerPrefix ready heap count.toNat := by
    rw [← hsEq,← countEq]
    exact complete
  exact callerPrefix.after_frame ready post heap count.toNat domainEq
    (fun slot _ => congrFun memoryEq _)

#print axioms validate_headers_body_returned_pointer_prefix
end InitECandidate.Runtime
