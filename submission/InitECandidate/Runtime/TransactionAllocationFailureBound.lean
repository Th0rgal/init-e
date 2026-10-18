import InitECandidate.Runtime.TransactionAllocationSuffixBound
import InitECandidate.Runtime.AllocationFailureDeclarationNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Exhausting the real heap rejects at the first decoder allocation within
two source ticks; no reserve for a successful allocation is required. -/
theorem transaction_allocation_failure_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (request : ((33806089496 : BitVec 64) - heap).toNat < 400)
    (budget : 2 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (transactionAt 2)
    state.clock ≤ evaluated.2.clock + 2 ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const 400] =
      some [.val (.word (400 : BitVec 64))] := rfl
  have terminal := evaluate_alloc_request_failure_declaration state (.const 400) heap 400
    (ofString "tx") .one (transactionAt 3) args code heapGlobal request
  have noTimeout := evaluate_alloc_request_failure_declaration_no_timeout state (.const 400) heap 400
    (ofString "tx") .one (transactionAt 3) args code heapGlobal request budget
  rw [source_transaction_allocation]
  dsimp only
  exact ⟨by rw [terminal.2]; omega,by rw [terminal.2]; omega,noTimeout,terminal.1⟩

/-- Natural heap geometry implies the actual unsigned allocator failure guard. -/
theorem transaction_allocation_failure_of_capacity {F : Type} (state : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (within : heap.toNat ≤ 33806089496) (exhausted : 33806089496 < heap.toNat + 400)
    (budget : 2 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (transactionAt 2)
    state.clock ≤ evaluated.2.clock + 2 ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  apply transaction_allocation_failure_bounded state heap code heapGlobal _ budget
  have difference : ((33806089496 : BitVec 64) - heap).toNat = 33806089496 - heap.toNat := by
    rw [BitVec.toNat_sub_of_le]
    · rfl
    · exact within
  rw [difference]
  omega

#print axioms transaction_allocation_failure_bounded
#print axioms transaction_allocation_failure_of_capacity
end InitECandidate.Runtime
