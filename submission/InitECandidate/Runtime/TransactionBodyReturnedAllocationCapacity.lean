import InitECandidate.Runtime.TransactionBodyReturnedAllocationWord
import InitECandidate.Runtime.TransactionAllocationSuffixBound
import InitECandidate.Runtime.AllocationReturnedGuard
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An actually returned decoder has passed its initial 400-byte allocation.
The capacity needed by successful-path contracts follows from this run rather
than an assumed worst-case reserve. No source-clock budget is needed. -/
theorem transaction_body_returned_allocation_capacity {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length heap : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (within : heap.toNat ≤ 33806089496)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_transaction_rlp) = (some (.returned value),post)) :
    (400 : BitVec 64) ≤ (33806089496 : BitVec 64) - heap ∧ heap.toNat + 400 ≤ 33806089496 := by
  obtain ⟨_,entry,output,byte,bodyRun,_,globals,entryCode,_,_,_,_,_⟩ :=
    transaction_body_returned_allocation_word state post pointer length value pointerLocal lengthLocal run
  rw [source_transaction_allocation] at bodyRun
  have request := alloc_declaration_returned_request entry output (.const 400) heap 400 (ofString "tx") .one
    (transactionAt 3) value (by rfl) (entryCode.trans code) (by rw [globals]; exact heapGlobal) bodyRun
  have capacity := allocationGuard_sum_bound heap 400 within request
  exact ⟨request,capacity⟩

#print axioms transaction_body_returned_allocation_capacity
end InitECandidate.Runtime
