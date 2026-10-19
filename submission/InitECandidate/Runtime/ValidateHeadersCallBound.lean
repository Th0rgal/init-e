import InitECandidate.Runtime.ValidateHeadersBodyBound
import InitECandidate.Runtime.RunAttemptHeadersEntry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- The installed original validation call adds one source entry tick; its
actual caller witness and memory geometry supply the full body premises. -/
theorem runBounded_validate_headers_call {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame heap keccakState keccakPad : BitVec 64) (ceiling inputLimit : Nat)
    (inputBound : inputLength.toNat ≤ inputLimit) (inputCap : inputLimit ≤ 134217712)
    (inputAfter : ceiling ≤ input.toNat) (tableAbove : ceiling ≤ array.toNat)
    (tableBefore : array.toNat + count.toNat * 16 ≤ heap.toNat)
    (inputBefore : input.toNat + inputLength.toNat ≤ heap.toNat)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (ceilingAligned : ceiling % 8 = 0) (stateBelow : keccakState.toNat + 200 ≤ ceiling) (padBelow : keccakPad.toNat + 136 ≤ ceiling)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite s (h := fun address => Classical.propDecidable (s.memaddrs address)) arguments =
      some [.val (.word array),.val (.word count)])
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (stateGlobal : s.globals.lookup (ofString "keccak_st") = some (.val (.word keccakState)))
    (padGlobal : s.globals.lookup (ofString "keccak_pad") = some (.val (.word keccakPad)))
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (heapArena : ∀ address : BitVec 64, heap.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (heapGlobal : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode)
    (budget : validateHeadersBodyCost inputLimit + 1 ≤ s.clock) :
    RunBounded s (.call (some (destination,none)) (ofString "validate_headers") arguments)
      (validateHeadersBodyCost inputLimit + 1) := by
  apply RunBounded.call (bodyCost := validateHeadersBodyCost inputLimit) args budget
  intro body callee shape lookup
  have installed : lookupCodeHOLFinite s.code.lookup (ofString "validate_headers")
      [.val (.word array),.val (.word count)] =
      some (sourceFunctionBody Guest.guestFn_validate_headers,validateHeadersCallee array count,.comb [.one,.one]) := by
    rw [code]
    exact lookup_validate_headers_callee array count
  rw [installed] at lookup
  obtain ⟨rfl,rfl,rfl⟩ := Option.some.inj lookup
  let entry := callEntryStateHOLFinite s (validateHeadersCallee array count)
  have atArray : entry.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simp (config := {decide := true}) [entry,callEntryStateHOLFinite,validateHeadersCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have atCount : entry.locals.lookup (ofString "n") = some (.val (.word count)) := by
    simp [entry,callEntryStateHOLFinite,validateHeadersCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryTable : RlpSliceInputPrefix entry array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨pointer,length,valid⟩ := table slot inside
    exact ⟨pointer,length,valid.after_frame s entry array slot pointer length input inputLength rfl rfl rfl⟩
  exact runBounded_validate_headers_body entry array count input inputLength scratch frame heap keccakState keccakPad ceiling inputLimit
    inputBound inputCap inputAfter tableAbove tableBefore inputBefore orderedFrame framePositive scratchBelow ceilingAligned stateBelow padBelow
    atArray atCount entryTable scratchGlobal frameGlobal stateGlobal padGlobal arena heapArena heapGlobal heapBound code
    (by change validateHeadersBodyCost inputLimit ≤ s.clock - 1; omega)

#print axioms runBounded_validate_headers_call
end InitECandidate.Runtime
