import InitECandidate.Runtime.AllocationAligned
import InitECandidate.Runtime.AllocationCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A naturally bounded array allocation executes the original allocator in
one source clock, without modifying the memory of earlier allocations. -/
theorem evaluate_allocation_product_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (pointer count width : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
        some [.val (.word (count * width))])
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (bounded : pointer.toNat + count.toNat * width.toNat + 7 ≤ 33806089496) :
    ∃ ready, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "alloc") [argument]) = (none,ready) ∧
      ready.clock = state.clock - 1 ∧ ready.memory = state.memory ∧ ready.locals = state.locals ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer (count * width)))) ∧
      pointer.toNat + count.toNat * width.toNat ≤ (allocationEnd pointer (count * width)).toNat ∧
      (allocationEnd pointer (count * width)).toNat ≤ 33806089496 ∧
      (allocationEnd pointer (count * width)).toNat % 8 = 0 := by
  have product := allocation_product_request pointer count width (by omega)
  have padded : pointer.toNat + (count * width).toNat + 7 ≤ 33806089496 := by
    rw [product.1]; exact bounded
  obtain ⟨guard,finish,cover,aligned⟩ := allocation_success_bounds pointer (count * width) padded
  obtain ⟨ready,run,ticks,memory,locals,_,_,_,_,globals,_⟩ :=
    evaluate_alloc_call_and_declaration state argument pointer (count * width) arguments code clock heapGlobal guard finish
  refine ⟨ready,run,ticks,memory,locals,?_,?_,finish,aligned⟩
  · rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simpa [product.1] using cover

#print axioms evaluate_allocation_product_call
end InitECandidate.Runtime
