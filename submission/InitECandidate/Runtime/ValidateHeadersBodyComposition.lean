import InitECandidate.Runtime.ValidateHeadersThroughFirstPhaseReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- Modular composition interface for the original full validation body.
The second-phase bound is an explicit premise, to be supplied by its checked
loop theorem; the entire real first phase is discharged here. -/
theorem runBounded_validate_headers_with_second_phase {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame heap keccakState keccakPad : BitVec 64) (ceiling inputLimit tailCost : Nat)
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
    (budget : 4 + validateHeadersFirstLoopCost inputLimit + tailCost ≤ s.clock)
    (secondPhase : ∀ (e : ValidateHeadersFirstEnvironment) (next : PanSemStateFiniteExact 64 F),
      e.array = array → e.count = count → e.input = input → e.inputLength = inputLength → e.inputLimit = inputLimit →
      e.hs = heap → e.hashes = allocationEnd heap (validateHeadersHsSize count) →
      ValidateHeadersFirstInvariant e next 0 → next.code = s.code → tailCost ≤ next.clock →
      RunBounded next (validateHeadersAt 5) tailCost) :
    RunBounded s (sourceFunctionBody Guest.guestFn_validate_headers)
      (4 + validateHeadersFirstLoopCost inputLimit + tailCost) := by
  rw [source_validate_headers_body]
  have firstPhase := validate_headers_through_first_phase_reaches s array count input inputLength scratch frame heap keccakState keccakPad ceiling inputLimit
    inputBound inputCap inputAfter tableAbove tableBefore inputBefore orderedFrame framePositive scratchBelow ceilingAligned stateBelow padBelow
    atArray atCount table scratchGlobal frameGlobal stateGlobal padGlobal arena heapArena heapGlobal heapBound code (by omega)
  apply RunBounded.ofReaches budget firstPhase
  intro next facts remaining
  obtain ⟨e,arrayEq,countEq,inputEq,lengthEq,limitEq,hsEq,hashEq,invariant,installed⟩ := facts
  exact secondPhase e next arrayEq countEq inputEq lengthEq limitEq hsEq hashEq invariant installed remaining

#print axioms runBounded_validate_headers_with_second_phase
end InitECandidate.Runtime
