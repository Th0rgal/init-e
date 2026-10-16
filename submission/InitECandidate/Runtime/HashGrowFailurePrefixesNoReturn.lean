import InitECandidate.Runtime.HashGrowFifthAllocationFailure
import InitECandidate.Runtime.HashGrowFourthAllocationFailure
import InitECandidate.Runtime.HashGrowThirdAllocationFailure
import InitECandidate.Runtime.HashGrowAllocationFailuresNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashGrow_second_allocation_failure_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer capacity stride : BitVec 64) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (capacityLocal : state.locals.lookup (ofString "ncap") = some (.val (.word capacity)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (pointerBound : pointer.toNat ≤ 33806089496) (clock : state.clock ≠ 0)
    (firstRequest : capacity * stride ≤ (33806089496 : BitVec 64) - pointer)
    (secondRequest : ((33806089496 : BitVec 64) - allocationEnd pointer (capacity * stride)).toNat < (capacity * 8).toNat) :
    ∀ returned : ValueHOL 64, (evaluateHOLFiniteState state (hashGrowKeysAllocation continuation)).1 ≠ some (.returned returned) := by
  intro returned
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.panop .mul [.var .local (ofString "ncap"),.var .local (ofString "stride")]] = some [.val (.word (capacity * stride))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capacityLocal,strideLocal,panOpHOL,valueIsWord,valueWord]
  obtain ⟨allocated,_,ticks,_,locals,postCode,_,_,_,globals,decl⟩ := evaluate_alloc_call_and_declaration state _ pointer (capacity * stride)
    arguments code clock heap firstRequest (allocationEnd_within_heap pointer (capacity * stride) pointerBound firstRequest)
  let entered := setVarHOLFinite (ofString "nkeys") (.val (.word pointer)) allocated
  have distinct : ofString "nkeys" ≠ ofString "ncap" := by decide
  have cap : entered.locals.lookup (ofString "ncap") = some (.val (.word capacity)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,distinct,locals,capacityLocal]
  have nextHeap : entered.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer (capacity * stride)))) := by
    change allocated.globals.lookup _ = _
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have failure := evaluate_hashGrow_values_allocation_failure_no_return entered (allocationEnd pointer (capacity * stride)) capacity stride continuation
    (postCode.trans code) nextHeap cap secondRequest
  unfold hashGrowKeysAllocation
  rw [decl]
  dsimp only
  exact failure returned

#print axioms evaluate_hashGrow_second_allocation_failure_no_return

theorem evaluate_hashGrow_values_used_failure_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer capacity stride : BitVec 64) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (capacityLocal : state.locals.lookup (ofString "ncap") = some (.val (.word capacity)))
    (pointerBound : pointer.toNat ≤ 33806089496) (clock : state.clock ≠ 0)
    (firstRequest : capacity * 8 ≤ (33806089496 : BitVec 64) - pointer)
    (secondRequest : ((33806089496 : BitVec 64) - allocationEnd pointer (capacity * 8)).toNat < (capacity).toNat) :
    ∀ returned : ValueHOL 64, (evaluateHOLFiniteState state (hashGrowValuesAllocation continuation)).1 ≠ some (.returned returned) := by
  intro returned
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
  have failure := evaluate_hashGrow_used_allocation_failure_no_return entered (allocationEnd pointer (capacity * 8)) capacity stride continuation
    (postCode.trans code) nextHeap cap secondRequest
  unfold hashGrowValuesAllocation
  rw [decl]
  dsimp only
  exact failure returned

#print axioms evaluate_hashGrow_values_used_failure_no_return

theorem evaluate_hashGrow_used_order_failure_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer capacity stride : BitVec 64) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (capacityLocal : state.locals.lookup (ofString "ncap") = some (.val (.word capacity)))
    (pointerBound : pointer.toNat ≤ 33806089496) (clock : state.clock ≠ 0)
    (firstRequest : capacity ≤ (33806089496 : BitVec 64) - pointer)
    (secondRequest : ((33806089496 : BitVec 64) - allocationEnd pointer (capacity)).toNat < (capacity * 8).toNat) :
    ∀ returned : ValueHOL 64, (evaluateHOLFiniteState state (hashGrowUsedAllocation continuation)).1 ≠ some (.returned returned) := by
  intro returned
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
  have failure := evaluate_hashGrow_order_allocation_failure_no_return entered (allocationEnd pointer (capacity)) capacity stride continuation
    (postCode.trans code) nextHeap cap secondRequest
  unfold hashGrowUsedAllocation
  rw [decl]
  dsimp only
  exact failure returned

#print axioms evaluate_hashGrow_used_order_failure_no_return

theorem evaluate_hashGrow_order_reverse_failure_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer capacity stride : BitVec 64) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (capacityLocal : state.locals.lookup (ofString "ncap") = some (.val (.word capacity)))
    (pointerBound : pointer.toNat ≤ 33806089496) (clock : state.clock ≠ 0)
    (firstRequest : capacity * 8 ≤ (33806089496 : BitVec 64) - pointer)
    (secondRequest : ((33806089496 : BitVec 64) - allocationEnd pointer (capacity * 8)).toNat < (capacity * 8).toNat) :
    ∀ returned : ValueHOL 64, (evaluateHOLFiniteState state (hashGrowOrderAllocation continuation)).1 ≠ some (.returned returned) := by
  intro returned
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
  have failure := evaluate_hashGrow_reverse_allocation_failure_no_return entered (allocationEnd pointer (capacity * 8)) capacity stride continuation
    (postCode.trans code) nextHeap cap secondRequest
  unfold hashGrowOrderAllocation
  rw [decl]
  dsimp only
  exact failure returned

#print axioms evaluate_hashGrow_order_reverse_failure_no_return

theorem evaluate_hashGrow_third_allocation_failure_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer capacity stride : BitVec 64) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (capacityLocal : state.locals.lookup (ofString "ncap") = some (.val (.word capacity)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (pointerBound : pointer.toNat ≤ 33806089496) (clock : 2 ≤ state.clock)
    (firstRequest : capacity * stride ≤ (33806089496 : BitVec 64) - pointer)
    (secondRequest : capacity * 8 ≤ (33806089496 : BitVec 64) - allocationEnd pointer (capacity * stride))
    (thirdRequest : ((33806089496 : BitVec 64) - allocationEnd (allocationEnd pointer (capacity * stride)) (capacity * 8)).toNat < capacity.toNat) :
    ∀ returned : ValueHOL 64, (evaluateHOLFiniteState state (hashGrowKeysAllocation continuation)).1 ≠ some (.returned returned) := by
  intro returned
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.panop .mul [.var .local (ofString "ncap"),.var .local (ofString "stride")]] = some [.val (.word (capacity * stride))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capacityLocal,strideLocal,panOpHOL,valueIsWord,valueWord]
  obtain ⟨allocated,_,ticks,_,locals,postCode,_,_,_,globals,decl⟩ := evaluate_alloc_call_and_declaration state _ pointer (capacity * stride)
    arguments code (by omega) heap firstRequest (allocationEnd_within_heap pointer (capacity * stride) pointerBound firstRequest)
  let entered := setVarHOLFinite (ofString "nkeys") (.val (.word pointer)) allocated
  have distinct : ofString "nkeys" ≠ ofString "ncap" := by decide
  have cap : entered.locals.lookup (ofString "ncap") = some (.val (.word capacity)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,distinct,locals,capacityLocal]
  have nextHeap : entered.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer (capacity * stride)))) := by
    change allocated.globals.lookup _ = _
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have failure := evaluate_hashGrow_values_used_failure_no_return entered (allocationEnd pointer (capacity * stride)) capacity stride continuation
    (postCode.trans code) nextHeap cap
    (allocationEnd_within_heap pointer (capacity * stride) pointerBound firstRequest)
    (by change allocated.clock ≠ 0; omega) secondRequest thirdRequest
  unfold hashGrowKeysAllocation
  rw [decl]
  dsimp only
  exact failure returned

#print axioms evaluate_hashGrow_third_allocation_failure_no_return

theorem evaluate_hashGrow_values_used_order_failure_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer capacity stride : BitVec 64) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (capacityLocal : state.locals.lookup (ofString "ncap") = some (.val (.word capacity)))
    (pointerBound : pointer.toNat ≤ 33806089496) (clock : 2 ≤ state.clock)
    (firstRequest : capacity * 8 ≤ (33806089496 : BitVec 64) - pointer)
    (secondRequest : capacity ≤ (33806089496 : BitVec 64) - allocationEnd pointer (capacity * 8))
    (thirdRequest : ((33806089496 : BitVec 64) - allocationEnd (allocationEnd pointer (capacity * 8)) (capacity)).toNat < (capacity * 8).toNat) :
    ∀ returned : ValueHOL 64, (evaluateHOLFiniteState state (hashGrowValuesAllocation continuation)).1 ≠ some (.returned returned) := by
  intro returned
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.panop .mul [.var .local (ofString "ncap"),.const 8]] = some [.val (.word (capacity * 8))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capacityLocal,panOpHOL,valueIsWord,valueWord]
  obtain ⟨allocated,_,ticks,_,locals,postCode,_,_,_,globals,decl⟩ := evaluate_alloc_call_and_declaration state _ pointer (capacity * 8)
    arguments code (by omega) heap firstRequest (allocationEnd_within_heap pointer (capacity * 8) pointerBound firstRequest)
  let entered := setVarHOLFinite (ofString "nvals") (.val (.word pointer)) allocated
  have distinct : ofString "nvals" ≠ ofString "ncap" := by decide
  have cap : entered.locals.lookup (ofString "ncap") = some (.val (.word capacity)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,distinct,locals,capacityLocal]
  have nextHeap : entered.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer (capacity * 8)))) := by
    change allocated.globals.lookup _ = _
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have failure := evaluate_hashGrow_used_order_failure_no_return entered (allocationEnd pointer (capacity * 8)) capacity stride continuation
    (postCode.trans code) nextHeap cap
    (allocationEnd_within_heap pointer (capacity * 8) pointerBound firstRequest)
    (by change allocated.clock ≠ 0; omega) secondRequest thirdRequest
  unfold hashGrowValuesAllocation
  rw [decl]
  dsimp only
  exact failure returned

#print axioms evaluate_hashGrow_values_used_order_failure_no_return

theorem evaluate_hashGrow_fourth_allocation_failure_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer capacity stride : BitVec 64) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (capacityLocal : state.locals.lookup (ofString "ncap") = some (.val (.word capacity)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (pointerBound : pointer.toNat ≤ 33806089496) (clock : 3 ≤ state.clock)
    (firstRequest : capacity * stride ≤ (33806089496 : BitVec 64) - pointer)
    (secondRequest : capacity * 8 ≤ (33806089496 : BitVec 64) - allocationEnd pointer (capacity * stride))
    (thirdRequest : capacity ≤ (33806089496 : BitVec 64) - allocationEnd (allocationEnd pointer (capacity * stride)) (capacity * 8))
    (fourthRequest : ((33806089496 : BitVec 64) - allocationEnd (allocationEnd (allocationEnd pointer (capacity * stride)) (capacity * 8)) capacity).toNat < (capacity * 8).toNat) :
    ∀ returned : ValueHOL 64, (evaluateHOLFiniteState state (hashGrowKeysAllocation continuation)).1 ≠ some (.returned returned) := by
  intro returned
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.panop .mul [.var .local (ofString "ncap"),.var .local (ofString "stride")]] = some [.val (.word (capacity * stride))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capacityLocal,strideLocal,panOpHOL,valueIsWord,valueWord]
  obtain ⟨allocated,_,ticks,_,locals,postCode,_,_,_,globals,decl⟩ := evaluate_alloc_call_and_declaration state _ pointer (capacity * stride)
    arguments code (by omega) heap firstRequest (allocationEnd_within_heap pointer (capacity * stride) pointerBound firstRequest)
  let entered := setVarHOLFinite (ofString "nkeys") (.val (.word pointer)) allocated
  have distinct : ofString "nkeys" ≠ ofString "ncap" := by decide
  have cap : entered.locals.lookup (ofString "ncap") = some (.val (.word capacity)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,distinct,locals,capacityLocal]
  have nextHeap : entered.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer (capacity * stride)))) := by
    change allocated.globals.lookup _ = _
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have failure := evaluate_hashGrow_values_used_order_failure_no_return entered (allocationEnd pointer (capacity * stride)) capacity stride continuation
    (postCode.trans code) nextHeap cap
    (allocationEnd_within_heap pointer (capacity * stride) pointerBound firstRequest)
    (by change 2 ≤ allocated.clock; omega) secondRequest thirdRequest fourthRequest
  unfold hashGrowKeysAllocation
  rw [decl]
  dsimp only
  exact failure returned

#print axioms evaluate_hashGrow_fourth_allocation_failure_no_return

theorem evaluate_hashGrow_used_order_reverse_failure_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer capacity stride : BitVec 64) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (capacityLocal : state.locals.lookup (ofString "ncap") = some (.val (.word capacity)))
    (pointerBound : pointer.toNat ≤ 33806089496) (clock : 2 ≤ state.clock)
    (firstRequest : capacity ≤ (33806089496 : BitVec 64) - pointer)
    (secondRequest : capacity * 8 ≤ (33806089496 : BitVec 64) - allocationEnd pointer (capacity))
    (thirdRequest : ((33806089496 : BitVec 64) - allocationEnd (allocationEnd pointer (capacity)) (capacity * 8)).toNat < (capacity * 8).toNat) :
    ∀ returned : ValueHOL 64, (evaluateHOLFiniteState state (hashGrowUsedAllocation continuation)).1 ≠ some (.returned returned) := by
  intro returned
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "ncap")] = some [.val (.word (capacity))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capacityLocal,panOpHOL,valueIsWord,valueWord]
  obtain ⟨allocated,_,ticks,_,locals,postCode,_,_,_,globals,decl⟩ := evaluate_alloc_call_and_declaration state _ pointer (capacity)
    arguments code (by omega) heap firstRequest (allocationEnd_within_heap pointer (capacity) pointerBound firstRequest)
  let entered := setVarHOLFinite (ofString "nused") (.val (.word pointer)) allocated
  have distinct : ofString "nused" ≠ ofString "ncap" := by decide
  have cap : entered.locals.lookup (ofString "ncap") = some (.val (.word capacity)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,distinct,locals,capacityLocal]
  have nextHeap : entered.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer (capacity)))) := by
    change allocated.globals.lookup _ = _
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have failure := evaluate_hashGrow_order_reverse_failure_no_return entered (allocationEnd pointer (capacity)) capacity stride continuation
    (postCode.trans code) nextHeap cap
    (allocationEnd_within_heap pointer (capacity) pointerBound firstRequest)
    (by change allocated.clock ≠ 0; omega) secondRequest thirdRequest
  unfold hashGrowUsedAllocation
  rw [decl]
  dsimp only
  exact failure returned

#print axioms evaluate_hashGrow_used_order_reverse_failure_no_return

theorem evaluate_hashGrow_values_used_order_reverse_failure_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer capacity stride : BitVec 64) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (capacityLocal : state.locals.lookup (ofString "ncap") = some (.val (.word capacity)))
    (pointerBound : pointer.toNat ≤ 33806089496) (clock : 3 ≤ state.clock)
    (firstRequest : capacity * 8 ≤ (33806089496 : BitVec 64) - pointer)
    (secondRequest : capacity ≤ (33806089496 : BitVec 64) - allocationEnd pointer (capacity * 8))
    (thirdRequest : capacity * 8 ≤ (33806089496 : BitVec 64) - allocationEnd (allocationEnd pointer (capacity * 8)) capacity)
    (fourthRequest : ((33806089496 : BitVec 64) - allocationEnd (allocationEnd (allocationEnd pointer (capacity * 8)) capacity) (capacity * 8)).toNat < (capacity * 8).toNat) :
    ∀ returned : ValueHOL 64, (evaluateHOLFiniteState state (hashGrowValuesAllocation continuation)).1 ≠ some (.returned returned) := by
  intro returned
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.panop .mul [.var .local (ofString "ncap"),.const 8]] = some [.val (.word (capacity * 8))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capacityLocal,panOpHOL,valueIsWord,valueWord]
  obtain ⟨allocated,_,ticks,_,locals,postCode,_,_,_,globals,decl⟩ := evaluate_alloc_call_and_declaration state _ pointer (capacity * 8)
    arguments code (by omega) heap firstRequest (allocationEnd_within_heap pointer (capacity * 8) pointerBound firstRequest)
  let entered := setVarHOLFinite (ofString "nvals") (.val (.word pointer)) allocated
  have distinct : ofString "nvals" ≠ ofString "ncap" := by decide
  have cap : entered.locals.lookup (ofString "ncap") = some (.val (.word capacity)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,distinct,locals,capacityLocal]
  have nextHeap : entered.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer (capacity * 8)))) := by
    change allocated.globals.lookup _ = _
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have failure := evaluate_hashGrow_used_order_reverse_failure_no_return entered (allocationEnd pointer (capacity * 8)) capacity stride continuation
    (postCode.trans code) nextHeap cap
    (allocationEnd_within_heap pointer (capacity * 8) pointerBound firstRequest)
    (by change 2 ≤ allocated.clock; omega) secondRequest thirdRequest fourthRequest
  unfold hashGrowValuesAllocation
  rw [decl]
  dsimp only
  exact failure returned

#print axioms evaluate_hashGrow_values_used_order_reverse_failure_no_return

theorem evaluate_hashGrow_fifth_allocation_failure_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer capacity stride : BitVec 64) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (capacityLocal : state.locals.lookup (ofString "ncap") = some (.val (.word capacity)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (pointerBound : pointer.toNat ≤ 33806089496) (clock : 4 ≤ state.clock)
    (firstRequest : capacity * stride ≤ (33806089496 : BitVec 64) - pointer)
    (secondRequest : capacity * 8 ≤ (33806089496 : BitVec 64) - allocationEnd pointer (capacity * stride))
    (thirdRequest : capacity ≤ (33806089496 : BitVec 64) - allocationEnd (allocationEnd pointer (capacity * stride)) (capacity * 8))
    (fourthRequest : capacity * 8 ≤ (33806089496 : BitVec 64) - allocationEnd (allocationEnd (allocationEnd pointer (capacity * stride)) (capacity * 8)) capacity)
    (fifthRequest : ((33806089496 : BitVec 64) - allocationEnd (allocationEnd (allocationEnd (allocationEnd pointer (capacity * stride)) (capacity * 8)) capacity) (capacity * 8)).toNat < (capacity * 8).toNat) :
    ∀ returned : ValueHOL 64, (evaluateHOLFiniteState state (hashGrowKeysAllocation continuation)).1 ≠ some (.returned returned) := by
  intro returned
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.panop .mul [.var .local (ofString "ncap"),.var .local (ofString "stride")]] = some [.val (.word (capacity * stride))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capacityLocal,strideLocal,panOpHOL,valueIsWord,valueWord]
  obtain ⟨allocated,_,ticks,_,locals,postCode,_,_,_,globals,decl⟩ := evaluate_alloc_call_and_declaration state _ pointer (capacity * stride)
    arguments code (by omega) heap firstRequest (allocationEnd_within_heap pointer (capacity * stride) pointerBound firstRequest)
  let entered := setVarHOLFinite (ofString "nkeys") (.val (.word pointer)) allocated
  have distinct : ofString "nkeys" ≠ ofString "ncap" := by decide
  have cap : entered.locals.lookup (ofString "ncap") = some (.val (.word capacity)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,distinct,locals,capacityLocal]
  have nextHeap : entered.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer (capacity * stride)))) := by
    change allocated.globals.lookup _ = _
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have failure := evaluate_hashGrow_values_used_order_reverse_failure_no_return entered (allocationEnd pointer (capacity * stride)) capacity stride continuation
    (postCode.trans code) nextHeap cap
    (allocationEnd_within_heap pointer (capacity * stride) pointerBound firstRequest)
    (by change 3 ≤ allocated.clock; omega) secondRequest thirdRequest fourthRequest fifthRequest
  unfold hashGrowKeysAllocation
  rw [decl]
  dsimp only
  exact failure returned

#print axioms evaluate_hashGrow_fifth_allocation_failure_no_return

end InitECandidate.Runtime
