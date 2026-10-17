import InitECandidate.Runtime.HashGrowUnsafeAllocationBound
import InitECandidate.Runtime.HashGrowFailurePrefixesNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashGrow_unsafe_allocations_no_timeout {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer capacity stride : BitVec 64) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (capacityLocal : state.locals.lookup (ofString "ncap") = some (.val (.word capacity)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (pointerBound : pointer.toNat ≤ 33806089496) (clock : 6 ≤ state.clock)
    (notSafe : ¬ AllocationPlanSafe pointer [capacity * stride,capacity * 8,capacity,capacity * 8,capacity * 8]) :
     (evaluateHOLFiniteState state (hashGrowKeysAllocation continuation)).1 ≠ some .timeOut := by
  have rejected : ∀ start size : BitVec 64, ¬size ≤ (33806089496 : BitVec 64) - start →
      ((33806089496 : BitVec 64) - start).toNat < size.toNat := by
    intro start size failure
    have notLe : ¬size.toNat ≤ ((33806089496 : BitVec 64) - start).toNat := fun le => failure (BitVec.le_def.mpr le)
    omega
  by_cases failed1 : ¬(capacity * stride ≤ (33806089496 : BitVec 64) - pointer)
  · have failure := evaluate_hashGrow_keys_allocation_failure_no_timeout state pointer capacity stride continuation code heap capacityLocal strideLocal (rejected _ _ failed1) (by omega)
    exact failure
  · have g1 : capacity * stride ≤ (33806089496 : BitVec 64) - pointer := Classical.not_not.mp failed1
    have b1 := allocationEnd_within_heap (pointer) (capacity * stride) pointerBound g1
    by_cases failed2 : ¬(capacity * 8 ≤ (33806089496 : BitVec 64) - (allocationEnd pointer (capacity * stride)))
    · have failure := evaluate_hashGrow_second_allocation_failure_no_timeout state pointer capacity stride continuation code heap capacityLocal strideLocal pointerBound (by omega) g1 (rejected _ _ failed2)
      exact failure
    · have g2 : capacity * 8 ≤ (33806089496 : BitVec 64) - (allocationEnd pointer (capacity * stride)) := Classical.not_not.mp failed2
      have b2 := allocationEnd_within_heap ((allocationEnd pointer (capacity * stride))) (capacity * 8) b1 g2
      by_cases failed3 : ¬(capacity ≤ (33806089496 : BitVec 64) - (allocationEnd (allocationEnd pointer (capacity * stride)) (capacity * 8)))
      · have failure := evaluate_hashGrow_third_allocation_failure_no_timeout state pointer capacity stride continuation code heap capacityLocal strideLocal pointerBound (by omega) g1 g2 (rejected _ _ failed3)
        exact failure
      · have g3 : capacity ≤ (33806089496 : BitVec 64) - (allocationEnd (allocationEnd pointer (capacity * stride)) (capacity * 8)) := Classical.not_not.mp failed3
        have b3 := allocationEnd_within_heap ((allocationEnd (allocationEnd pointer (capacity * stride)) (capacity * 8))) (capacity) b2 g3
        by_cases failed4 : ¬(capacity * 8 ≤ (33806089496 : BitVec 64) - (allocationEnd (allocationEnd (allocationEnd pointer (capacity * stride)) (capacity * 8)) (capacity)))
        · have failure := evaluate_hashGrow_fourth_allocation_failure_no_timeout state pointer capacity stride continuation code heap capacityLocal strideLocal pointerBound (by omega) g1 g2 g3 (rejected _ _ failed4)
          exact failure
        · have g4 : capacity * 8 ≤ (33806089496 : BitVec 64) - (allocationEnd (allocationEnd (allocationEnd pointer (capacity * stride)) (capacity * 8)) (capacity)) := Classical.not_not.mp failed4
          have b4 := allocationEnd_within_heap ((allocationEnd (allocationEnd (allocationEnd pointer (capacity * stride)) (capacity * 8)) (capacity))) (capacity * 8) b3 g4
          by_cases failed5 : ¬(capacity * 8 ≤ (33806089496 : BitVec 64) - (allocationEnd (allocationEnd (allocationEnd (allocationEnd pointer (capacity * stride)) (capacity * 8)) (capacity)) (capacity * 8)))
          · have failure := evaluate_hashGrow_fifth_allocation_failure_no_timeout state pointer capacity stride continuation code heap capacityLocal strideLocal pointerBound (by omega) g1 g2 g3 g4 (rejected _ _ failed5)
            exact failure
          · have g5 : capacity * 8 ≤ (33806089496 : BitVec 64) - (allocationEnd (allocationEnd (allocationEnd (allocationEnd pointer (capacity * stride)) (capacity * 8)) (capacity)) (capacity * 8)) := Classical.not_not.mp failed5
            have b5 := allocationEnd_within_heap ((allocationEnd (allocationEnd (allocationEnd (allocationEnd pointer (capacity * stride)) (capacity * 8)) (capacity)) (capacity * 8))) (capacity * 8) b4 g5
            exact False.elim (notSafe ⟨g1,b1,g2,b2,g3,b3,g4,b4,g5,b5,b5⟩)

#print axioms evaluate_hashGrow_unsafe_allocations_no_timeout
end InitECandidate.Runtime
