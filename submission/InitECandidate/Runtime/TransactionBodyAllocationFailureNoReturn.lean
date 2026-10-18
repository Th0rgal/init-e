import InitECandidate.Runtime.TransactionBodyReturnedAllocationWord
import InitECandidate.Runtime.AllocationFailureDeclarationNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_allocation_failure_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (request : ((33806089496 : BitVec 64) - heap).toNat < 400) (value : ValueHOL 64) :
    (evaluateHOLFiniteState state (transactionAt 2)).1 ≠ some (.returned value) := by
  rw [source_transaction_allocation]
  exact evaluate_alloc_request_failure_declaration_no_return state (.const 400) heap 400
    (ofString "tx") .one (transactionAt 3) value rfl code heapGlobal request

/-- Exhaustion cannot return a transaction pointer to a caller continuation,
regardless of the available source clock or the input bytes. -/
theorem transaction_body_allocation_failure_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length heap : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (request : ((33806089496 : BitVec 64) - heap).toNat < 400) (value : ValueHOL 64) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_transaction_rlp)).1 ≠ some (.returned value) := by
  intro equal
  cases run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_transaction_rlp) with
  | mk result post =>
    rw [run] at equal
    dsimp only at equal
    subst result
    obtain ⟨_,entry,output,byte,bodyRun,_,globals,entryCode,_,_,_,_,_⟩ := transaction_body_returned_allocation_word
      state post pointer length value pointerLocal lengthLocal run
    have noReturn := transaction_allocation_failure_no_return entry heap (entryCode.trans code)
      (by rw [globals]; exact heapGlobal) request value
    rw [bodyRun] at noReturn
    exact noReturn rfl

#print axioms transaction_allocation_failure_no_return
#print axioms transaction_body_allocation_failure_no_return
end InitECandidate.Runtime
