import InitECandidate.Runtime.AllocationBodyBound
import InitECandidate.Runtime.AllocationFailureCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual allocator calls consume at most two source clocks for every request:
one call entry and, on failure, one trap call entry. -/
theorem evaluate_alloc_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (pointer size : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] = some [.val (.word size)])
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496) :
    state.clock ≤ (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "alloc") [argument])).2.clock + 2 ∧
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "alloc") [argument])).2.clock ≤ state.clock := by
  by_cases zero : state.clock = 0
  · have installed : state.code.lookup (ofString "alloc") =
        some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_alloc,.one) := by
      rw [code]; exact originalRuntimeCode_allocation_lookup
    have lookup := pan_single_word_lookup state.code.lookup (ofString "alloc") (ofString "n")
      (sourceFunctionBody Guest.guestFn_alloc) size installed
    rw [evaluateHOLFiniteState_call,arguments]
    dsimp only
    rw [lookup]
    simp [zero,emptyLocalsHOLFinite]
  · by_cases request : size ≤ (33806089496 : BitVec 64) - pointer
    · obtain ⟨ready,run,clock,_⟩ := evaluate_alloc_call_and_declaration state argument pointer size arguments code zero heap request
        (allocationEnd_within_heap pointer size pointerBound request)
      rw [run]
      dsimp only
      omega
    · have rejected : ((33806089496 : BitVec 64) - pointer).toNat < size.toNat := by
        have notLe : ¬size.toNat ≤ ((33806089496 : BitVec 64) - pointer).toNat := fun le => request (BitVec.le_def.mpr le)
        omega
      have clock := (evaluate_alloc_request_failure_call state argument pointer size arguments code heap rejected).2
      rw [clock]
      omega

#print axioms evaluate_alloc_call_bounded
end InitECandidate.Runtime
