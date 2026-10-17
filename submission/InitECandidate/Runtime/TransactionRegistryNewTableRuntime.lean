import InitECandidate.Runtime.HashNewCallHeapAllRequests
import InitECandidate.Runtime.TransactionRegistryHeapBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A live transaction supplies every heap premise of the complete constructor
runtime bound, including allocation rejection. This asserts runtime only;
registry extension after success is a separate invariant obligation. -/
theorem TransactionRegistryWorld.new_table_runtime_all_requests {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (fieldPointer ts journal snapshot count pointer keyLength capacity : BitVec 64)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (destination : Option (VarKind × MlS)) (keyArgument capacityArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [keyArgument,capacityArgument] = some [.val (.word keyLength),.val (.word capacity)])
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (ticks : capacity.toNat + 9 ≤ state.clock) :
    let output := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "htab_new") [keyArgument,capacityArgument]);
    output.1 ≠ some .timeOut ∧
      state.clock ≤ output.2.clock + capacity.toNat + 9 ∧ output.2.clock ≤ state.clock := by
  exact evaluate_htabNew_call_heap_all_requests state pointer keyLength capacity destination keyArgument capacityArgument
    arguments valid.journalWorld.code ticks heap (valid.heap_bounded pointer heap) valid.journalWorld.heapDomain

/-- The literal storage constructor has a seventeen-clock bound in every live
transaction, with no reserve premise and regardless of heap exhaustion. -/
theorem TransactionRegistryWorld.new_storage_table_runtime_all_requests {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (fieldPointer ts journal snapshot count pointer : BitVec 64)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (destination : Option (VarKind × MlS))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (ticks : 17 ≤ state.clock) :
    let output := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "htab_new") [.const 32,.const 8]);
    output.1 ≠ some .timeOut ∧ state.clock ≤ output.2.clock + 17 ∧ output.2.clock ≤ state.clock := by
  have runtime := TransactionRegistryWorld.new_table_runtime_all_requests state widths tables fieldPointer ts journal snapshot count pointer 32 8 valid
    destination (.const 32) (.const 8) rfl heap ticks
  dsimp only at runtime ⊢
  exact ⟨runtime.1,by have cost := runtime.2.1; change state.clock ≤ _ + 8 + 9 at cost; omega,runtime.2.2⟩

#print axioms TransactionRegistryWorld.new_table_runtime_all_requests
#print axioms TransactionRegistryWorld.new_storage_table_runtime_all_requests
end InitECandidate.Runtime
