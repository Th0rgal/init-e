import InitECandidate.Runtime.HashTableSetUnsafeBound32
import InitECandidate.Runtime.HashTableSetWithGrowthLinkedEntries32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Uniform original set bound without an allocation-plan success assumption. -/
theorem HashTableReady32.set_body_bounded {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (strideBound : stride.toNat ≤ 56)
    (ticks : 3 * capacity.toNat + 2 * (capacity * 2).toNat + 44 + items.toNat * ((capacity * 2).toNat + 36) ≤ state.clock)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (capacityLarge : 1 < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).1 ≠ none ∧
      state.clock ≤ (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).2.clock +
        3 * capacity.toNat + 2 * (capacity * 2).toNat + 44 + items.toNat * ((capacity * 2).toNat + 36) ∧
      (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).2.clock ≤ state.clock := by
  by_cases safe : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride)
  · obtain ⟨post,run,_,cost,remaining,_⟩ := ready.live.arrays.set_with_growth_safe_plan_linked_entries state
      table pointer keys stride capacity used values order orderPos items key value bits ready.live.entries ready.valuesWord ready.reverse ready.linked
      ready.ordering ready.live.frontier.allocated strideBound ready.live.frontier.aligned ready.live.frontier.bounded
      (ready.live.arrays.capacity_bounded state table keys stride capacity used values order orderPos items bits)
      safe (by omega) ready.live.frontier.heap domain tableLocal keyLocal valueLocal capacityLarge keyAligned sourceWordDomain sourceByteDomain
    rw [run]
    dsimp only
    exact ⟨by simp,by omega,remaining⟩
  · by_cases below : (items.toNat + 1) * 2 ≤ capacity.toNat
    · obtain ⟨_,post,_,run,_,_,_,_,_,cost,remaining,_⟩ :=
        ready.live.arrays.set_no_growth_linked_entries state table keys stride capacity used values order orderPos items key value bits
          tableLocal keyLocal valueLocal keyAligned sourceWordDomain sourceByteDomain below (by omega)
          ready.valuesWord ready.reverse ready.live.entries ready.linked ready.ordering
      rw [run]
      dsimp only
      exact ⟨by simp,by omega,remaining⟩
    · have keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset) := by
        intro offset member
        apply sourceWordDomain
        simp at member
        omega
      have failure := ready.set_unsafe_above state table pointer keys stride capacity used values order orderPos items key value bits
        tableLocal keyLocal valueLocal keyAligned keyDomain (by omega) safe (by omega)
      exact ⟨failure.1,by have cost := failure.2.1; omega,failure.2.2⟩

#print axioms HashTableReady32.set_body_bounded
end InitECandidate.Runtime
