import InitECandidate.Runtime.HashNewCallUnsafeTerminal
import InitECandidate.Runtime.TransactionStorageTableExactSpace
import InitECandidate.Runtime.StateStorageTerminalConstructor
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- With fewer than 528 remaining bytes, the original missing-inner branch
terminates at constructor rejection and skips both journal updates. -/
theorem TransactionRegistryWorld.storage_new_inner_insufficient_space {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (fieldPointer ts journal snapshot count pointer lookupValue : BitVec 64)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (mLocal : state.locals.lookup (ofString "m") = some (.rStruct [.val (.word (0 : BitVec 64)),.val (.word lookupValue)]))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (shortage : ¬pointer.toNat + 528 ≤ 33806089496) (ticks : 17 ≤ state.clock) :
    let output := evaluateHOLFiniteState state stateStorageInnerSelection;
    output.1 ≠ none ∧ output.1 ≠ some .timeOut ∧ (∀ value, output.1 ≠ some (.returned value)) ∧
      state.clock ≤ output.2.clock + 17 ∧ output.2.clock ≤ state.clock := by
  have pointerBound := valid.heap_bounded pointer heap
  have planRejected : ¬AllocationPlanSafe pointer (htabNewAllocationSizes 32 8) := by
    intro safe
    exact shortage ((storageTable_safe_plan_iff pointer pointerBound (valid.heap_facts pointer heap).1).mp safe)
  have failure := evaluate_htabNew_call_heap_unsafe_terminal state pointer 32 8 (some (.local,ofString "inner"))
    (.const 32) (.const 8) rfl valid.journalWorld.code ticks heap pointerBound valid.journalWorld.heapDomain planRejected
  have run := evaluate_storage_new_inner_terminal_constructor state lookupValue mLocal failure.1
  dsimp only
  rw [run]
  refine ⟨failure.1,failure.2.1,failure.2.2.1,?_,failure.2.2.2.2⟩
  have cost := failure.2.2.2.1
  change state.clock ≤ _ + 8 + 9 at cost
  omega

#print axioms TransactionRegistryWorld.storage_new_inner_insufficient_space
end InitECandidate.Runtime
