import InitECandidate.Runtime.HashNewArraysOrderFrontier32
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The current heap pointer lies beyond a table's final array, is aligned,
and remains within the original heap limit. -/
structure HashTableHeapFrontier32 {F : Type} (orderPos capacity pointer : BitVec 64)
    (state : PanSemStateFiniteExact 64 F) : Prop where
  heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer))
  allocated : orderPos.toNat + capacity.toNat * 8 ≤ pointer.toNat
  bounded : pointer.toNat ≤ 33806089496
  aligned : pointer.toNat % 8 = 0

theorem HashTableHeapFrontier32.after_globals {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (orderPos capacity pointer : BitVec 64)
    (frontier : HashTableHeapFrontier32 orderPos capacity pointer state)
    (globals : post.globals = state.globals) :
    HashTableHeapFrontier32 orderPos capacity pointer post := by
  exact ⟨by rw [globals]; exact frontier.heap,frontier.allocated,frontier.bounded,frontier.aligned⟩

/-- Other successful allocations retain the frontier condition for earlier
tables whenever the heap pointer advances and remains aligned and bounded. -/
theorem HashTableHeapFrontier32.advance {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (orderPos capacity pointer next : BitVec 64)
    (frontier : HashTableHeapFrontier32 orderPos capacity pointer state)
    (heap : post.globals.lookup (ofString "heap_ptr") = some (.val (.word next)))
    (monotone : pointer.toNat ≤ next.toNat) (bounded : next.toNat ≤ 33806089496)
    (aligned : next.toNat % 8 = 0) : HashTableHeapFrontier32 orderPos capacity next post := by
  exact ⟨heap,by have := frontier.allocated; omega,bounded,aligned⟩

/-- The constructor's exact heap result establishes a frontier for its arrays. -/
theorem htabNew_heap_frontier32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table capacity : BitVec 64)
    (budget : table.toNat + 81 * capacity.toNat + 114 ≤ 33806089496)
    (heap : state.globals.lookup (ofString "heap_ptr") =
      some (.val (.word (allocationEnd (htabNewOrderPos table 32 capacity) (capacity * 8))))) :
    HashTableHeapFrontier32 (htabNewOrderPos table 32 capacity) capacity
      (allocationEnd (htabNewOrderPos table 32 capacity) (capacity * 8)) state := by
  have facts := htabNew_frontier_facts table 32 capacity (by decide) budget
  exact ⟨heap,facts.1,facts.2.1,facts.2.2⟩

#print axioms HashTableHeapFrontier32.after_globals
#print axioms HashTableHeapFrontier32.advance
#print axioms htabNew_heap_frontier32
end InitECandidate.Runtime
