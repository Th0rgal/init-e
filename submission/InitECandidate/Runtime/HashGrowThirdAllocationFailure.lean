import InitECandidate.Runtime.HashGrowAdjacentAllocationFailures
import InitECandidate.Runtime.AllocationBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Two successful key/value allocations followed by an excessive occupancy request stop the original growth allocation suffix within four clocks. -/
theorem evaluate_hashGrow_third_allocation_failure {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer capacity stride : BitVec 64) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (capacityLocal : state.locals.lookup (ofString "ncap") = some (.val (.word capacity)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (pointerBound : pointer.toNat ≤ 33806089496) (clock : 2 ≤ state.clock)
    (firstRequest : capacity * stride ≤ (33806089496 : BitVec 64) - pointer)
    (secondRequest : capacity * 8 ≤ (33806089496 : BitVec 64) - allocationEnd pointer (capacity * stride))
    (thirdRequest : ((33806089496 : BitVec 64) - allocationEnd (allocationEnd pointer (capacity * stride)) (capacity * 8)).toNat < capacity.toNat) :
    (evaluateHOLFiniteState state (hashGrowKeysAllocation continuation)).1 ≠ none ∧
    (evaluateHOLFiniteState state (hashGrowKeysAllocation continuation)).2.clock = state.clock - 4 := by
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
  have failure := evaluate_hashGrow_values_used_failure entered (allocationEnd pointer (capacity * stride)) capacity stride continuation
    (postCode.trans code) nextHeap cap
    (allocationEnd_within_heap pointer (capacity * stride) pointerBound firstRequest)
    (by change allocated.clock ≠ 0; omega) secondRequest thirdRequest
  unfold hashGrowKeysAllocation
  rw [decl]
  dsimp only
  refine ⟨failure.1,?_⟩
  change (evaluateHOLFiniteState entered (hashGrowValuesAllocation continuation)).2.clock = state.clock - 4
  rw [failure.2]
  change allocated.clock - 3 = state.clock - 4
  rw [ticks]
  omega

#print axioms evaluate_hashGrow_third_allocation_failure
end InitECandidate.Runtime
