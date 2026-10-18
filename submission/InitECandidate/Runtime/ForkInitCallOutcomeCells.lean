import InitECandidate.Runtime.ForkInitCallOutcome
import InitECandidate.Runtime.AlignedCellDomains
import InitECandidate.Runtime.MemzeroAlignedCallCells
import InitECandidate.Runtime.KeccakShortCallBoundCells
import InitECandidate.Runtime.ForkInitBodyReturnedCells
import InitECandidate.Runtime.ForkInitCallBoundCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem evaluate_forkInit_call_outcome_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer oldZero oldPrecompile : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (zeroSlot : state.globals.lookup (ofString "zero32") = some (.val (.word oldZero)))
    (precompileSlot : state.globals.lookup (ofString "precompile_addrs") = some (.val (.word oldPrecompile)))
    (words : ∀ entry ∈ forkSuffixAllocations, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (aligned : pointer.toNat % 8 = 0)
    (small : pointer.toNat + 592 ≤ 33806089496)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → pointer.toNat ≤ address.toNat →
      address.toNat < pointer.toNat + 392 → state.memaddrs address)
    (budget : 516 ≤ state.clock) :
    let result := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "fork_init") [])
    state.clock ≤ result.2.clock + 516 ∧ result.2.clock ≤ state.clock ∧ result.1 ≠ some .timeOut ∧
      (result.1 = none → result.2.globals = globalAllocationGlobals state.globals pointer forkInitAllocations ∧
        result.2.locals = state.locals ∧ result.2.code = state.code ∧ result.2.memaddrs = state.memaddrs ∧
        ∃ finalHeap : BitVec 64, result.2.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
          finalHeap.toNat = pointer.toNat + 592) := by
  have bounded := evaluate_forkInit_call_bounded_cells state none [] pointer oldZero oldPrecompile
    code heap zeroSlot precompileSlot aligned (by omega) arena budget
  refine ⟨bounded.1,bounded.2.1,bounded.2.2,?_⟩
  intro normal
  have lookup := pan_no_args_lookup state.code.lookup (ofString "fork_init")
    (sourceFunctionBody Guest.guestFn_fork_init) (by rw [code]; exact originalRuntimeCode_forkInit_lookup)
  have nonzero : state.clock ≠ 0 := by omega
  revert normal
  rw [evaluateHOLFiniteState_call]
  simp only [evalListHOLFinite,evalListHOLExact]
  rw [lookup]
  simp only [if_neg nonzero]
  cases run : evaluateHOLFiniteState (callEntryStateHOLFinite state HolFiniteMapExact.empty)
      (sourceFunctionBody Guest.guestFn_fork_init) with
  | mk result post =>
    rcases result with _ | (_ | _ | _ | _ | w | _ | _)
    all_goals first
      | (simp; done)
      | skip
    obtain ⟨_,globals,finalHeap,heapEnd,heapNat⟩ := evaluate_forkInit_body_returned_globals_cells
      (callEntryStateHOLFinite state HolFiniteMapExact.empty) pointer oldZero oldPrecompile w
      code heap zeroSlot precompileSlot words aligned small arena
      (by change 515 ≤ state.clock - 1; omega) (by rw [run])
    rw [run] at globals heapEnd
    have metadata := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state HolFiniteMapExact.empty)
      (sourceFunctionBody Guest.guestFn_fork_init)
    rw [run] at metadata
    dsimp only
    split
    · intro _
      exact ⟨globals,rfl,metadata.1,metadata.2.1,finalHeap,heapEnd,heapNat⟩
    · simp

#print axioms evaluate_forkInit_call_outcome_cells
end InitECandidate.Runtime
