import InitECandidate.Runtime.HashGrowAdjacentAllocationFailures
import InitECandidate.Runtime.AllocationBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Occupancy and order allocation success followed by reverse-order allocation failure costs four clocks from the occupancy allocation scope. -/
theorem evaluate_hashGrow_used_order_reverse_failure {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer capacity stride : BitVec 64) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (capacityLocal : state.locals.lookup (ofString "ncap") = some (.val (.word capacity)))
    (pointerBound : pointer.toNat ≤ 33806089496) (clock : 2 ≤ state.clock)
    (firstRequest : capacity ≤ (33806089496 : BitVec 64) - pointer)
    (secondRequest : capacity * 8 ≤ (33806089496 : BitVec 64) - allocationEnd pointer (capacity))
    (thirdRequest : ((33806089496 : BitVec 64) - allocationEnd (allocationEnd pointer (capacity)) (capacity * 8)).toNat < (capacity * 8).toNat) :
    (evaluateHOLFiniteState state (hashGrowUsedAllocation continuation)).1 ≠ none ∧
    (evaluateHOLFiniteState state (hashGrowUsedAllocation continuation)).2.clock = state.clock - 4 := by
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
  have failure := evaluate_hashGrow_order_reverse_failure entered (allocationEnd pointer (capacity)) capacity stride continuation
    (postCode.trans code) nextHeap cap
    (allocationEnd_within_heap pointer (capacity) pointerBound firstRequest)
    (by change allocated.clock ≠ 0; omega) secondRequest thirdRequest
  unfold hashGrowUsedAllocation
  rw [decl]
  dsimp only
  refine ⟨failure.1,?_⟩
  change (evaluateHOLFiniteState entered (hashGrowOrderAllocation continuation)).2.clock = state.clock - 4
  rw [failure.2]
  change allocated.clock - 3 = state.clock - 4
  rw [ticks]
  omega

#print axioms evaluate_hashGrow_used_order_reverse_failure
end InitECandidate.Runtime
