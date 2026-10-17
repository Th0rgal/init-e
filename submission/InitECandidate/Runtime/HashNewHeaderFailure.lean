import InitECandidate.Runtime.HashNewHeader
import InitECandidate.Runtime.AllocationFailureDeclarationNoTimeout
import InitECandidate.Runtime.AllocationFailureDeclarationNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Rejection of the constructor's first header allocation prevents all later
allocations and zeroing. The actual body exits in exactly two clocks. -/
theorem evaluate_htabNew_header_allocation_failure {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (rejected : ((33806089496 : BitVec 64) - pointer).toNat < 72)
    (ticks : 2 ≤ state.clock) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_new)).1 ≠ none ∧
      (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_new)).1 ≠ some .timeOut ∧
      (∀ value, (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_new)).1 ≠ some (.returned value)) ∧
      (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_new)).2.clock = state.clock - 2 := by
  rw [source_htabNew_header]
  have failure := evaluate_alloc_request_failure_declaration state (.const 72) pointer 72 (ofString "t") .one
    (.dec (ofString "stride") .one htabNewStrideExpression (htabNewHeader htabNewAfterHeader)) rfl code heap rejected
  have noTimeout := evaluate_alloc_request_failure_declaration_no_timeout state (.const 72) pointer 72 (ofString "t") .one
    (.dec (ofString "stride") .one htabNewStrideExpression (htabNewHeader htabNewAfterHeader)) rfl code heap rejected ticks
  refine ⟨failure.1,noTimeout,?_,failure.2⟩
  intro value
  exact evaluate_alloc_request_failure_declaration_no_return state (.const 72) pointer 72 (ofString "t") .one
    (.dec (ofString "stride") .one htabNewStrideExpression (htabNewHeader htabNewAfterHeader)) value rfl code heap rejected

#print axioms evaluate_htabNew_header_allocation_failure
end InitECandidate.Runtime
