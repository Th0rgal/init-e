import InitECandidate.Runtime.HashNewUsedAllocation
import InitECandidate.Runtime.HashNewOrderTail
import InitECandidate.Runtime.AllocationFailureDeclarationNoTimeout
import InitECandidate.Runtime.AllocationFailureDeclarationNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Rejection of the values allocation skips its complete remaining suffix. -/
theorem evaluate_htabNew_values_allocation_failure {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer capacity : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (rejected : ((33806089496 : BitVec 64) - pointer).toNat < (capacity * 8).toNat)
    (ticks : 2 ≤ state.clock) :
    (evaluateHOLFiniteState state htabNewValuesAllocation).1 ≠ none ∧
      (evaluateHOLFiniteState state htabNewValuesAllocation).1 ≠ some .timeOut ∧
      (∀ value, (evaluateHOLFiniteState state htabNewValuesAllocation).1 ≠ some (.returned value)) ∧
      (evaluateHOLFiniteState state htabNewValuesAllocation).2.clock = state.clock - 2 := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [(.panop .mul [.var .local (ofString "cap"),.const 8])] = some [.val (.word (capacity * 8))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capLocal,panOpHOL,valueIsWord,valueWord]
  have failure := evaluate_alloc_request_failure_declaration state (.panop .mul [.var .local (ofString "cap"),.const 8]) pointer (capacity * 8) (ofString "vals") .one (.seq (.store (hashLocalAddress (ofString "t") 40) (.var .local (ofString "vals"))) htabNewUsedAllocation) args code heap rejected
  have noTimeout := evaluate_alloc_request_failure_declaration_no_timeout state (.panop .mul [.var .local (ofString "cap"),.const 8]) pointer (capacity * 8) (ofString "vals") .one (.seq (.store (hashLocalAddress (ofString "t") 40) (.var .local (ofString "vals"))) htabNewUsedAllocation) args code heap rejected ticks
  rw [source_htabNew_values_allocation]
  refine ⟨failure.1,noTimeout,?_,failure.2⟩
  intro value
  exact evaluate_alloc_request_failure_declaration_no_return state (.panop .mul [.var .local (ofString "cap"),.const 8]) pointer (capacity * 8) (ofString "vals") .one (.seq (.store (hashLocalAddress (ofString "t") 40) (.var .local (ofString "vals"))) htabNewUsedAllocation) value args code heap rejected

#print axioms evaluate_htabNew_values_allocation_failure

/-- Rejection of the used allocation skips its complete remaining suffix. -/
theorem evaluate_htabNew_used_allocation_failure {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer capacity : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (rejected : ((33806089496 : BitVec 64) - pointer).toNat < capacity.toNat)
    (ticks : 2 ≤ state.clock) :
    (evaluateHOLFiniteState state htabNewUsedAllocation).1 ≠ none ∧
      (evaluateHOLFiniteState state htabNewUsedAllocation).1 ≠ some .timeOut ∧
      (∀ value, (evaluateHOLFiniteState state htabNewUsedAllocation).1 ≠ some (.returned value)) ∧
      (evaluateHOLFiniteState state htabNewUsedAllocation).2.clock = state.clock - 2 := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [(.var .local (ofString "cap"))] = some [.val (.word capacity)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capLocal]
  have failure := evaluate_alloc_request_failure_declaration state (.var .local (ofString "cap")) pointer capacity (ofString "used") .one htabNewUsedBody args code heap rejected
  have noTimeout := evaluate_alloc_request_failure_declaration_no_timeout state (.var .local (ofString "cap")) pointer capacity (ofString "used") .one htabNewUsedBody args code heap rejected ticks
  unfold htabNewUsedAllocation
  refine ⟨failure.1,noTimeout,?_,failure.2⟩
  intro value
  exact evaluate_alloc_request_failure_declaration_no_return state (.var .local (ofString "cap")) pointer capacity (ofString "used") .one htabNewUsedBody value args code heap rejected

#print axioms evaluate_htabNew_used_allocation_failure

/-- Rejection of the order allocation skips its complete remaining suffix. -/
theorem evaluate_htabNew_order_allocation_failure {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer capacity : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (rejected : ((33806089496 : BitVec 64) - pointer).toNat < (capacity * 8).toNat)
    (ticks : 2 ≤ state.clock) :
    (evaluateHOLFiniteState state htabNewAfterZero).1 ≠ none ∧
      (evaluateHOLFiniteState state htabNewAfterZero).1 ≠ some .timeOut ∧
      (∀ value, (evaluateHOLFiniteState state htabNewAfterZero).1 ≠ some (.returned value)) ∧
      (evaluateHOLFiniteState state htabNewAfterZero).2.clock = state.clock - 2 := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [(.panop .mul [.var .local (ofString "cap"),.const 8])] = some [.val (.word (capacity * 8))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capLocal,panOpHOL,valueIsWord,valueWord]
  have failure := evaluate_alloc_request_failure_declaration state (.panop .mul [.var .local (ofString "cap"),.const 8]) pointer (capacity * 8) (ofString "order") .one (.seq (.store (hashLocalAddress (ofString "t") 56) (.var .local (ofString "order"))) htabNewFinalAllocation) args code heap rejected
  have noTimeout := evaluate_alloc_request_failure_declaration_no_timeout state (.panop .mul [.var .local (ofString "cap"),.const 8]) pointer (capacity * 8) (ofString "order") .one (.seq (.store (hashLocalAddress (ofString "t") 56) (.var .local (ofString "order"))) htabNewFinalAllocation) args code heap rejected ticks
  rw [source_htabNew_order_tail]
  refine ⟨failure.1,noTimeout,?_,failure.2⟩
  intro value
  exact evaluate_alloc_request_failure_declaration_no_return state (.panop .mul [.var .local (ofString "cap"),.const 8]) pointer (capacity * 8) (ofString "order") .one (.seq (.store (hashLocalAddress (ofString "t") 56) (.var .local (ofString "order"))) htabNewFinalAllocation) value args code heap rejected

#print axioms evaluate_htabNew_order_allocation_failure

/-- Rejection of the reverse allocation skips its complete remaining suffix. -/
theorem evaluate_htabNew_reverse_allocation_failure {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer capacity : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (rejected : ((33806089496 : BitVec 64) - pointer).toNat < (capacity * 8).toNat)
    (ticks : 2 ≤ state.clock) :
    (evaluateHOLFiniteState state htabNewFinalAllocation).1 ≠ none ∧
      (evaluateHOLFiniteState state htabNewFinalAllocation).1 ≠ some .timeOut ∧
      (∀ value, (evaluateHOLFiniteState state htabNewFinalAllocation).1 ≠ some (.returned value)) ∧
      (evaluateHOLFiniteState state htabNewFinalAllocation).2.clock = state.clock - 2 := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [(.panop .mul [.var .local (ofString "cap"),.const 8])] = some [.val (.word (capacity * 8))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capLocal,panOpHOL,valueIsWord,valueWord]
  have failure := evaluate_alloc_request_failure_declaration state (.panop .mul [.var .local (ofString "cap"),.const 8]) pointer (capacity * 8) (ofString "order_pos") .one (.seq (.store (hashLocalAddress (ofString "t") 64) (.var .local (ofString "order_pos"))) (.return (.var .local (ofString "t")))) args code heap rejected
  have noTimeout := evaluate_alloc_request_failure_declaration_no_timeout state (.panop .mul [.var .local (ofString "cap"),.const 8]) pointer (capacity * 8) (ofString "order_pos") .one (.seq (.store (hashLocalAddress (ofString "t") 64) (.var .local (ofString "order_pos"))) (.return (.var .local (ofString "t")))) args code heap rejected ticks
  rw [source_htabNew_final_allocation]
  refine ⟨failure.1,noTimeout,?_,failure.2⟩
  intro value
  exact evaluate_alloc_request_failure_declaration_no_return state (.panop .mul [.var .local (ofString "cap"),.const 8]) pointer (capacity * 8) (ofString "order_pos") .one (.seq (.store (hashLocalAddress (ofString "t") 64) (.var .local (ofString "order_pos"))) (.return (.var .local (ofString "t")))) value args code heap rejected

#print axioms evaluate_htabNew_reverse_allocation_failure

end InitECandidate.Runtime
