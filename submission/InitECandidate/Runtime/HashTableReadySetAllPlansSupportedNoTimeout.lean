import InitECandidate.Runtime.HashTableReadySetBodySupported
import InitECandidate.Runtime.HashTableReadySetUnsafeGrowthSupportedNoTimeout
import InitECandidate.Runtime.HashTableGrowOldArraysWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableReady.set_body_supported_all_plans_no_timeout {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (initial : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (strideBound : stride.toNat ≤ 56) (pointerAligned : pointer.toNat % 8 = 0)
    (pointerBound : pointer.toNat ≤ 33806089496)
    (capacityBound : capacity.toNat ≤ 33806089496)
    (ticks : 2 * capacity.toNat + 2 * (capacity * 2).toNat + keyLength.toNat + 12 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (capacityLarge : 1 < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).1 ≠ none ∧
      (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).1 ≠ some .timeOut ∧
      state.clock ≤ (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).2.clock +
        2 * capacity.toNat + 2 * (capacity * 2).toNat + keyLength.toNat + 12 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ∧
      (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).2.clock ≤ state.clock := by
  classical
  by_cases safe : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride)
  · have old := initial.live.arrays.old_arrays_width state keyLength table keys stride capacity used values order orderPos items bits pointer.toNat
      initial.live.entries initial.live.frontier.allocated pointerBound
    have headerBefore : table.toNat + 72 ≤ pointer.toNat := by
      have h := old.headerOrder
      have e := old.orderEnd
      omega
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,limit⟩ := htabGrow_array_layout_from_safe_plan table pointer capacity stride
      strideBound pointerAligned headerBefore pointerBound capacityBound safe
    have allocatedDomain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
        address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address := by
      intro address lower upper
      exact domain address lower (by omega)
    obtain ⟨post,run,_,cost,remaining,_⟩ := initial.set_body_supported_safe_plan state keyLength table pointer keys stride capacity used values order orderPos items key value bits supported
      strideBound pointerAligned pointerBound capacityBound safe ticks heap allocatedDomain tableLocal keyLocal valueLocal capacityLarge keyAligned sourceWordDomain sourceByteDomain
    rw [run]
    dsimp only
    exact ⟨by simp,by simp,cost,remaining⟩
  · by_cases below : (items.toNat + 1) * 2 ≤ capacity.toNat
    · have doubled : (capacity * (2 : BitVec 64)).toNat = 2 * capacity.toNat := by
        rw [BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)]
        change capacity.toNat * 2 = 2 * capacity.toNat
        omega
      obtain ⟨_,post,_,run,_,cost,remaining,_⟩ := initial.set_body_no_growth_supported state keyLength table pointer keys stride capacity used values order orderPos items key value bits supported
        tableLocal keyLocal valueLocal keyAligned sourceWordDomain sourceByteDomain below (by rw [doubled] at ticks; omega)
      rw [run]
      dsimp only
      exact ⟨by simp,by simp,by rw [doubled]; omega,remaining⟩
    · have failure := initial.set_unsafe_growth_supported_no_timeout state keyLength table pointer keys stride capacity used values order orderPos items key value bits supported
        tableLocal keyLocal valueLocal keyAligned sourceWordDomain sourceByteDomain (by omega) heap pointerBound safe (by omega)
      exact ⟨failure.1,failure.2.1,by have cost := failure.2.2.1; omega,failure.2.2.2⟩

#print axioms HashTableReady.set_body_supported_all_plans_no_timeout
end InitECandidate.Runtime
