import InitECandidate.Runtime.HashTableReadySetBodyHeapFrameSupported
import InitECandidate.Runtime.HashTableReadySetUnsafeGrowthSupportedDichotomy
import InitECandidate.Runtime.HashSetRegistryCostCeiling
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful original set bodies preserve every non-heap global, across
no-growth, safe-growth and unsafe-growth lookup outcomes. -/
theorem HashTableReady.set_body_all_plans_success_heap_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order reverse items key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order reverse items bits pointer state)
    (small : stride.toNat ≤ 56) (large : 1 < capacity.toNat)
    (budget : hashSetRegistryCost capacity keyLength items ≤ state.clock)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (k : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (v : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (aligned : key.toNat % 8 = 0)
    (words : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (returnedValue : ValueHOL 64)
    (success : (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).1 = some (.returned returnedValue)) :
    HeapGlobalsFrame state (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).2 := by
  have numeric : 3 * capacity.toNat + 2 * (capacity * 2).toNat + keyLength.toNat + 13 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ≤ state.clock := budget
  by_cases below : (items.toNat + 1) * 2 ≤ capacity.toNat
  · obtain ⟨nextCount,post,_,run,_,_,_,globals,_⟩ := ready.set_body_no_growth_supported state keyLength table pointer keys stride capacity used values order reverse items key value bits supported t k v aligned words bytes below (by omega)
    rw [run]
    exact HeapGlobalsFrame.of_globals globals
  · by_cases safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride)
    · have capacityBound : capacity.toNat ≤ 33806089496 := by
        have := ready.live.arrays.usedBefore
        have := ready.live.arrays.orderBefore
        have := ready.live.arrays.endBound
        omega
      have headerBefore : table.toNat + 72 ≤ pointer.toNat := by
        have := ready.live.arrays.headerKeys
        have := ready.live.arrays.keysBefore
        have := ready.live.arrays.usedBefore
        have := ready.live.arrays.orderBefore
        have := ready.live.frontier.allocated
        omega
      have domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat → address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address := by
        intro address lower upper
        obtain ⟨_,_,_,_,_,_,_,_,_,_,_,limit⟩ := htabGrow_array_layout_from_safe_plan table pointer capacity stride small ready.live.frontier.aligned headerBefore ready.live.frontier.bounded capacityBound safePlan
        exact heapDomain address (by omega)
      obtain ⟨post,run,_,_,_,_,_,_,frame⟩ := ready.set_body_supported_heap_frame state keyLength table pointer keys stride capacity used values order reverse items key value bits supported small
        ready.live.frontier.aligned ready.live.frontier.bounded capacityBound safePlan (by omega) ready.live.frontier.heap domain t k v large aligned words bytes
      rw [run]
      exact frame
    · rcases ready.set_unsafe_growth_supported_dichotomy state keyLength table pointer keys stride capacity used values order reverse items key value bits supported t k v aligned words bytes
        (by omega) ready.live.frontier.heap ready.live.frontier.bounded safePlan (by omega) with good | failure
      · obtain ⟨post,run,_,globals,_⟩ := good
        rw [run]
        exact HeapGlobalsFrame.of_globals globals
      · exact False.elim (failure.2.2.1 returnedValue success)

#print axioms HashTableReady.set_body_all_plans_success_heap_frame
end InitECandidate.Runtime
