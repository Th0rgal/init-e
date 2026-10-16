import InitECandidate.Runtime.HashTableSetWithGrowthSafePlan32
import InitECandidate.Runtime.HashTableSetUnsafeGrowthBound32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableArraysInvariant32.set_all_plans_bounded {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos items bits state)
    (entries : HashOrderEntriesBound order capacity items state)
    (allocated : orderPos.toNat + capacity.toNat * 8 ≤ pointer.toNat)
    (strideBound : stride.toNat ≤ 56) (pointerAligned : pointer.toNat % 8 = 0)
    (pointerBound : pointer.toNat ≤ 33806089496)
    (capacityBound : capacity.toNat ≤ 33806089496)
    (ticks : 2 * capacity.toNat + 2 * (capacity * 2).toNat + 44 + items.toNat * ((capacity * 2).toNat + 36) ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (capacityLarge : 1 < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).1 ≠ none ∧
    state.clock ≤ (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).2.clock +
      2 * capacity.toNat + 2 * (capacity * 2).toNat + 44 + items.toNat * ((capacity * 2).toNat + 36) ∧
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).2.clock ≤ state.clock := by
  classical
  by_cases safe : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride)
  · have old := invariant.old_arrays state table keys stride capacity used values order orderPos items bits pointer.toNat entries allocated pointerBound
    have headerBefore : table.toNat + 72 ≤ pointer.toNat := by
      have := old.headerOrder
      have := old.orderEnd
      omega
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,limit⟩ := htabGrow_array_layout_from_safe_plan table pointer capacity stride
      strideBound pointerAligned headerBefore pointerBound capacityBound safe
    have allocatedDomain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
        address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address := by
      intro address lower upper
      exact domain address lower (by omega)
    obtain ⟨post,run,_,cost,remaining,_⟩ := invariant.set_with_growth_safe_plan state table pointer keys stride capacity used values order orderPos items key value bits
      entries allocated strideBound pointerAligned pointerBound capacityBound safe ticks heap allocatedDomain tableLocal keyLocal valueLocal capacityLarge keyAligned sourceWordDomain sourceByteDomain
    rw [run]
    dsimp only
    exact ⟨by simp,cost,remaining⟩
  · by_cases below : (items.toNat + 1) * 2 ≤ capacity.toNat
    · have doubled : (capacity * (2 : BitVec 64)).toNat = 2 * capacity.toNat := by
        rw [BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)]
        change capacity.toNat * 2 = 2 * capacity.toNat
        omega
      obtain ⟨_,post,_,run,_,_,cost,remaining,_⟩ := invariant.set_no_growth_order state table keys stride capacity used values order orderPos items key value bits
        tableLocal keyLocal valueLocal keyAligned sourceWordDomain sourceByteDomain below (by rw [doubled] at ticks; omega) entries
      rw [run]
      dsimp only
      exact ⟨by simp,by rw [doubled]; omega,remaining⟩
    · have keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset) := by
        intro offset member
        apply sourceWordDomain
        simp at member
        omega
      have failure := invariant.set_unsafe_growth_bounded state table pointer keys stride capacity used values order orderPos items key value bits
        tableLocal keyLocal valueLocal keyAligned keyDomain (by omega) heap pointerBound safe (by omega)
      exact ⟨failure.1,by have := failure.2.1; omega,failure.2.2⟩

#print axioms HashTableArraysInvariant32.set_all_plans_bounded
end InitECandidate.Runtime
