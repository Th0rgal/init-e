import InitECandidate.Runtime.RipemdInitReturned
import InitECandidate.Runtime.AllocationInitializersCallBound
import InitECandidate.Runtime.PanNoArgsLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The original RIPEMD call is uniformly bounded, with exact normal-return
allocation globals and a 456-byte heap advance on first initialization. -/
theorem evaluate_ripemdInit_call_outcome {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (zero : state.globals.lookup (ofString "rmd_tab") = some (.val (.word 0)))
    (words : ∀ entry ∈ ripemdInitAllocations, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (aligned : pointer.toNat % 8 = 0) (small : pointer.toNat + 456 ≤ 33806089496)
    (budget : 9 ≤ state.clock) :
    let result := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "ripemd160_init") [])
    state.clock ≤ result.2.clock + 9 ∧ result.2.clock ≤ state.clock ∧ result.1 ≠ some .timeOut ∧
      (result.1 = none → result.2.globals = globalAllocationGlobals state.globals pointer ripemdInitAllocations ∧
        result.2.locals = state.locals ∧ result.2.code = state.code ∧ result.2.memaddrs = state.memaddrs ∧
        ∃ finalHeap : BitVec 64, result.2.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
          finalHeap.toNat = pointer.toNat + 456) := by
  have bounded := evaluate_ripemd160Init_call_bounded state none [] code budget
  refine ⟨bounded.1,bounded.2.1,bounded.2.2,?_⟩
  intro normal
  have lookup := pan_no_args_lookup state.code.lookup (ofString "ripemd160_init")
    (sourceFunctionBody Guest.guestFn_ripemd160_init) (by rw [code]; exact originalRuntimeCode_ripemd160Init_lookup)
  have nonzero : state.clock ≠ 0 := by omega
  revert normal
  rw [evaluateHOLFiniteState_call]
  simp only [evalListHOLFinite,evalListHOLExact]
  rw [lookup]
  simp only [if_neg nonzero]
  cases run : evaluateHOLFiniteState (callEntryStateHOLFinite state HolFiniteMapExact.empty)
      (sourceFunctionBody Guest.guestFn_ripemd160_init) with
  | mk result post =>
    rcases result with _ | (_ | _ | _ | _ | w | _ | _)
    all_goals first
      | (simp; done)
      | skip
    obtain ⟨_,globals,finalHeap,heapEnd,heapNat⟩ := evaluate_ripemdInit_body_returned_globals
      (callEntryStateHOLFinite state HolFiniteMapExact.empty) post pointer w code heap zero words aligned small run
    have metadata := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state HolFiniteMapExact.empty)
      (sourceFunctionBody Guest.guestFn_ripemd160_init)
    rw [run] at metadata
    dsimp only
    split
    · intro _
      exact ⟨globals,rfl,metadata.1,metadata.2.1,finalHeap,heapEnd,heapNat⟩
    · simp

#print axioms evaluate_ripemdInit_call_outcome
end InitECandidate.Runtime
