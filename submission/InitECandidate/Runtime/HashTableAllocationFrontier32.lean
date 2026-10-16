import InitECandidate.Runtime.HashTableHeapFrontier32
import InitECandidate.Runtime.AllocationCall
import InitECandidate.Runtime.AllocationBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An actual successful allocation advances the frontier of an already live
table and preserves its memory, including its order entries. -/
theorem HashTableHeapFrontier32.alloc_call {F : Type}
    (state : PanSemStateFiniteExact 64 F) (orderPos capacity pointer size : BitVec 64)
    (argument : ExpHOL 64)
    (frontier : HashTableHeapFrontier32 orderPos capacity pointer state)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
        some [.val (.word size)])
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (request : size ≤ (33806089496 : BitVec 64) - pointer) :
    ∃ post, evaluateHOLFiniteState state
        (.call (some (none,none)) (ofString "alloc") [argument]) = (none,post) ∧
      HashTableHeapFrontier32 orderPos capacity (allocationEnd pointer size) post ∧
      post.clock = state.clock - 1 ∧ post.memory = state.memory ∧
      post.locals = state.locals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.eshapes = state.eshapes ∧ post.be = state.be := by
  have bounded := allocationEnd_within_heap pointer size frontier.bounded request
  have covers := allocationEnd_covers pointer size
    (allocationGuard_sum_bound pointer size frontier.bounded request)
  obtain ⟨post,run,ticks,memory,locals,postCode,domain,shapes,endian,globals,_⟩ :=
    evaluate_alloc_call_and_declaration state argument pointer size arguments code clock
      frontier.heap request bounded
  have heap : post.globals.lookup (ofString "heap_ptr") =
      some (.val (.word (allocationEnd pointer size))) := by
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have advanced := frontier.advance state post orderPos capacity pointer
    (allocationEnd pointer size) heap (by omega) bounded covers.2.2
  exact ⟨post,run,advanced,ticks,memory,locals,postCode,domain,shapes,endian⟩

#print axioms HashTableHeapFrontier32.alloc_call
end InitECandidate.Runtime
