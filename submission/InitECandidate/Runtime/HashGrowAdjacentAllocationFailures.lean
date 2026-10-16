import InitECandidate.Runtime.HashGrowSecondAllocationFailure
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashGrow_values_used_failure {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer capacity stride : BitVec 64) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (capacityLocal : state.locals.lookup (ofString "ncap") = some (.val (.word capacity)))
    (pointerBound : pointer.toNat ≤ 33806089496) (clock : state.clock ≠ 0)
    (firstRequest : capacity * 8 ≤ (33806089496 : BitVec 64) - pointer)
    (secondRequest : ((33806089496 : BitVec 64) - allocationEnd pointer (capacity * 8)).toNat < (capacity).toNat) :
    (evaluateHOLFiniteState state (hashGrowValuesAllocation continuation)).1 ≠ none ∧
    (evaluateHOLFiniteState state (hashGrowValuesAllocation continuation)).2.clock = state.clock - 3 := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.panop .mul [.var .local (ofString "ncap"),.const 8]] = some [.val (.word (capacity * 8))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capacityLocal,panOpHOL,valueIsWord,valueWord]
  obtain ⟨allocated,_,ticks,_,locals,postCode,_,_,_,globals,decl⟩ := evaluate_alloc_call_and_declaration state _ pointer (capacity * 8)
    arguments code clock heap firstRequest (allocationEnd_within_heap pointer (capacity * 8) pointerBound firstRequest)
  let entered := setVarHOLFinite (ofString "nvals") (.val (.word pointer)) allocated
  have distinct : ofString "nvals" ≠ ofString "ncap" := by decide
  have cap : entered.locals.lookup (ofString "ncap") = some (.val (.word capacity)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,distinct,locals,capacityLocal]
  have nextHeap : entered.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer (capacity * 8)))) := by
    change allocated.globals.lookup _ = _
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have failure := evaluate_hashGrow_used_allocation_failure entered (allocationEnd pointer (capacity * 8)) capacity stride continuation
    (postCode.trans code) nextHeap cap secondRequest
  unfold hashGrowValuesAllocation
  rw [decl]
  dsimp only
  refine ⟨failure.1,?_⟩
  change (evaluateHOLFiniteState entered (hashGrowUsedAllocation continuation)).2.clock = state.clock - 3
  rw [failure.2]
  change allocated.clock - 2 = state.clock - 3
  rw [ticks]
  omega


#print axioms evaluate_hashGrow_values_used_failure

theorem evaluate_hashGrow_used_order_failure {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer capacity stride : BitVec 64) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (capacityLocal : state.locals.lookup (ofString "ncap") = some (.val (.word capacity)))
    (pointerBound : pointer.toNat ≤ 33806089496) (clock : state.clock ≠ 0)
    (firstRequest : capacity ≤ (33806089496 : BitVec 64) - pointer)
    (secondRequest : ((33806089496 : BitVec 64) - allocationEnd pointer (capacity)).toNat < (capacity * 8).toNat) :
    (evaluateHOLFiniteState state (hashGrowUsedAllocation continuation)).1 ≠ none ∧
    (evaluateHOLFiniteState state (hashGrowUsedAllocation continuation)).2.clock = state.clock - 3 := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "ncap")] = some [.val (.word (capacity))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capacityLocal,panOpHOL,valueIsWord,valueWord]
  obtain ⟨allocated,_,ticks,_,locals,postCode,_,_,_,globals,decl⟩ := evaluate_alloc_call_and_declaration state _ pointer (capacity)
    arguments code clock heap firstRequest (allocationEnd_within_heap pointer (capacity) pointerBound firstRequest)
  let entered := setVarHOLFinite (ofString "nused") (.val (.word pointer)) allocated
  have distinct : ofString "nused" ≠ ofString "ncap" := by decide
  have cap : entered.locals.lookup (ofString "ncap") = some (.val (.word capacity)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,distinct,locals,capacityLocal]
  have nextHeap : entered.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer (capacity)))) := by
    change allocated.globals.lookup _ = _
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have failure := evaluate_hashGrow_order_allocation_failure entered (allocationEnd pointer (capacity)) capacity stride continuation
    (postCode.trans code) nextHeap cap secondRequest
  unfold hashGrowUsedAllocation
  rw [decl]
  dsimp only
  refine ⟨failure.1,?_⟩
  change (evaluateHOLFiniteState entered (hashGrowOrderAllocation continuation)).2.clock = state.clock - 3
  rw [failure.2]
  change allocated.clock - 2 = state.clock - 3
  rw [ticks]
  omega


#print axioms evaluate_hashGrow_used_order_failure

theorem evaluate_hashGrow_order_reverse_failure {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer capacity stride : BitVec 64) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (capacityLocal : state.locals.lookup (ofString "ncap") = some (.val (.word capacity)))
    (pointerBound : pointer.toNat ≤ 33806089496) (clock : state.clock ≠ 0)
    (firstRequest : capacity * 8 ≤ (33806089496 : BitVec 64) - pointer)
    (secondRequest : ((33806089496 : BitVec 64) - allocationEnd pointer (capacity * 8)).toNat < (capacity * 8).toNat) :
    (evaluateHOLFiniteState state (hashGrowOrderAllocation continuation)).1 ≠ none ∧
    (evaluateHOLFiniteState state (hashGrowOrderAllocation continuation)).2.clock = state.clock - 3 := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.panop .mul [.var .local (ofString "ncap"),.const 8]] = some [.val (.word (capacity * 8))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capacityLocal,panOpHOL,valueIsWord,valueWord]
  obtain ⟨allocated,_,ticks,_,locals,postCode,_,_,_,globals,decl⟩ := evaluate_alloc_call_and_declaration state _ pointer (capacity * 8)
    arguments code clock heap firstRequest (allocationEnd_within_heap pointer (capacity * 8) pointerBound firstRequest)
  let entered := setVarHOLFinite (ofString "norder") (.val (.word pointer)) allocated
  have distinct : ofString "norder" ≠ ofString "ncap" := by decide
  have cap : entered.locals.lookup (ofString "ncap") = some (.val (.word capacity)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,distinct,locals,capacityLocal]
  have nextHeap : entered.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer (capacity * 8)))) := by
    change allocated.globals.lookup _ = _
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have failure := evaluate_hashGrow_reverse_allocation_failure entered (allocationEnd pointer (capacity * 8)) capacity stride continuation
    (postCode.trans code) nextHeap cap secondRequest
  unfold hashGrowOrderAllocation
  rw [decl]
  dsimp only
  refine ⟨failure.1,?_⟩
  change (evaluateHOLFiniteState entered (.decCall (ofString "norder_pos") .one (ofString "alloc")
      [.panop .mul [.var .local (ofString "ncap"),.const 8]] (hashGrowZeroHeader continuation))).2.clock = state.clock - 3
  rw [failure.2]
  change allocated.clock - 2 = state.clock - 3
  rw [ticks]
  omega


#print axioms evaluate_hashGrow_order_reverse_failure
end InitECandidate.Runtime
