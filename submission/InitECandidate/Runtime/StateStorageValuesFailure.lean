import InitECandidate.Runtime.StorageTableValuesFailureCall
import InitECandidate.Runtime.StateStorageTerminalConstructor
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original missing-inner storage branch exits in five clocks when
its constructor rejects the values array, bypassing both journal updates. -/
theorem evaluate_storage_new_inner_values_failure {F : Type}
    (state : PanSemStateFiniteExact 64 F) (pointer lookupValue : BitVec 64)
    (mLocal : state.locals.lookup (ofString "m") = some (.rStruct [.val (.word (0 : BitVec 64)),.val (.word lookupValue)]))
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (headerRequest : (72 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (headerFinish : (allocationEnd pointer 72).toNat ≤ 33806089496)
    (keysRequest : (256 : BitVec 64) ≤ (33806089496 : BitVec 64) - allocationEnd pointer 72)
    (keysFinish : (allocationEnd (allocationEnd pointer 72) 256).toNat ≤ 33806089496)
    (domain0 : state.memaddrs (pointer + 0)) (domain8 : state.memaddrs (pointer + 8))
    (domain16 : state.memaddrs (pointer + 16)) (domain24 : state.memaddrs (pointer + 24))
    (domain32 : state.memaddrs (pointer + 32))
    (valuesRejected : ((33806089496 : BitVec 64) - allocationEnd (allocationEnd pointer 72) 256).toNat < 64)
    (ticks : 5 ≤ state.clock) :
    let output := evaluateHOLFiniteState state stateStorageInnerSelection;
    output.1 ≠ none ∧ output.1 ≠ some .timeOut ∧ (∀ value, output.1 ≠ some (.returned value)) ∧
      output.2.clock = state.clock - 5 := by
  have failure := evaluate_storage_table_values_failure_call state pointer (some (.local,ofString "inner")) code heap
    headerRequest headerFinish keysRequest keysFinish domain0 domain8 domain16 domain24 domain32 valuesRejected ticks
  have run := evaluate_storage_new_inner_terminal_constructor state lookupValue mLocal failure.1
  dsimp only
  rw [run]
  exact failure

#print axioms evaluate_storage_new_inner_values_failure
end InitECandidate.Runtime
