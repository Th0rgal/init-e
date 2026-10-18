import InitECandidate.Runtime.VersionedHashesAllocationFailureBound
import InitECandidate.Runtime.TransactionWrapperDeclCallAllocationFailureControl
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Initial heap exhaustion prevents both another transaction iteration and
a hash-comparison return; invalid argument loads are terminal as well. -/
theorem versioned_hashes_allocation_failure_control {F : Type} (state : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (request : ((33806089496 : BitVec 64) - heap).toNat < 400) :
    (evaluateHOLFiniteState state versionedHashesStep).1 ≠ none ∧
    (∀ value, (evaluateHOLFiniteState state versionedHashesStep).1 ≠ some (.returned value)) := by
  rcases transaction_slice_arguments_word_result state (ofString "txs") (ofString "i") with missing | ⟨pointer,length,args⟩
  · rw [evaluate_versioned_hashes_source_step_missing_arguments state missing]
    simp
  · rw [source_versioned_hashes_step]
    exact transaction_wrapper_decl_call_allocation_failure_control state (ofString "tx") .one
      (transactionSliceArguments (ofString "txs") (ofString "i")) _ pointer length heap args code heapGlobal request

#print axioms versioned_hashes_allocation_failure_control
end InitECandidate.Runtime
