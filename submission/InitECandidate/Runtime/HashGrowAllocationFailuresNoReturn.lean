import InitECandidate.Runtime.HashGrowAllocationFailures
import InitECandidate.Runtime.AllocationFailureDeclarationNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashGrow_keys_allocation_failure_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer capacity stride : BitVec 64) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (capacityLocal : state.locals.lookup (ofString "ncap") = some (.val (.word capacity)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (request : ((33806089496 : BitVec 64) - pointer).toNat < (capacity * stride).toNat) :
    ∀ returned : ValueHOL 64, (evaluateHOLFiniteState state (hashGrowKeysAllocation continuation)).1 ≠ some (.returned returned) := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.panop .mul [.var .local (ofString "ncap"),.var .local (ofString "stride")]] = some [.val (.word (capacity * stride))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capacityLocal,strideLocal,panOpHOL,valueIsWord,valueWord]
  intro returned
  exact evaluate_alloc_request_failure_declaration_no_return state _ pointer (capacity * stride) (ofString "nkeys") .one
    (hashGrowValuesAllocation continuation) returned arguments code heap request


#print axioms evaluate_hashGrow_keys_allocation_failure_no_return

theorem evaluate_hashGrow_values_allocation_failure_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer capacity stride : BitVec 64) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (capacityLocal : state.locals.lookup (ofString "ncap") = some (.val (.word capacity)))
    (request : ((33806089496 : BitVec 64) - pointer).toNat < (capacity * 8).toNat) :
    ∀ returned : ValueHOL 64, (evaluateHOLFiniteState state (hashGrowValuesAllocation continuation)).1 ≠ some (.returned returned) := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.panop .mul [.var .local (ofString "ncap"),.const 8]] = some [.val (.word (capacity * 8))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capacityLocal,panOpHOL,valueIsWord,valueWord]
  intro returned
  exact evaluate_alloc_request_failure_declaration_no_return state _ pointer (capacity * 8) (ofString "nvals") .one
    (hashGrowUsedAllocation continuation) returned arguments code heap request


#print axioms evaluate_hashGrow_values_allocation_failure_no_return

theorem evaluate_hashGrow_used_allocation_failure_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer capacity stride : BitVec 64) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (capacityLocal : state.locals.lookup (ofString "ncap") = some (.val (.word capacity)))
    (request : ((33806089496 : BitVec 64) - pointer).toNat < (capacity).toNat) :
    ∀ returned : ValueHOL 64, (evaluateHOLFiniteState state (hashGrowUsedAllocation continuation)).1 ≠ some (.returned returned) := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.var .local (ofString "ncap")] = some [.val (.word (capacity))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capacityLocal,panOpHOL,valueIsWord,valueWord]
  intro returned
  exact evaluate_alloc_request_failure_declaration_no_return state _ pointer (capacity) (ofString "nused") .one
    (hashGrowOrderAllocation continuation) returned arguments code heap request


#print axioms evaluate_hashGrow_used_allocation_failure_no_return

theorem evaluate_hashGrow_order_allocation_failure_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer capacity stride : BitVec 64) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (capacityLocal : state.locals.lookup (ofString "ncap") = some (.val (.word capacity)))
    (request : ((33806089496 : BitVec 64) - pointer).toNat < (capacity * 8).toNat) :
    ∀ returned : ValueHOL 64, (evaluateHOLFiniteState state (hashGrowOrderAllocation continuation)).1 ≠ some (.returned returned) := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.panop .mul [.var .local (ofString "ncap"),.const 8]] = some [.val (.word (capacity * 8))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capacityLocal,panOpHOL,valueIsWord,valueWord]
  intro returned
  exact evaluate_alloc_request_failure_declaration_no_return state _ pointer (capacity * 8) (ofString "norder") .one
    (_) returned arguments code heap request


#print axioms evaluate_hashGrow_order_allocation_failure_no_return

theorem evaluate_hashGrow_reverse_allocation_failure_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer capacity stride : BitVec 64) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (capacityLocal : state.locals.lookup (ofString "ncap") = some (.val (.word capacity)))
    (request : ((33806089496 : BitVec 64) - pointer).toNat < (capacity * 8).toNat) :
    ∀ returned : ValueHOL 64, (evaluateHOLFiniteState state (.decCall (ofString "norder_pos") .one (ofString "alloc")
      [.panop .mul [.var .local (ofString "ncap"),.const 8]] (hashGrowZeroHeader continuation))).1 ≠ some (.returned returned) := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.panop .mul [.var .local (ofString "ncap"),.const 8]] = some [.val (.word (capacity * 8))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capacityLocal,panOpHOL,valueIsWord,valueWord]
  intro returned
  exact evaluate_alloc_request_failure_declaration_no_return state _ pointer (capacity * 8) (ofString "norder_pos") .one
    (hashGrowZeroHeader continuation) returned arguments code heap request


#print axioms evaluate_hashGrow_reverse_allocation_failure_no_return

end InitECandidate.Runtime
