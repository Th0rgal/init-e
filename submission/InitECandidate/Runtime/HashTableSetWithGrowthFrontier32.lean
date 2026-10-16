import InitECandidate.Runtime.HashTableSetAboveThresholdFrontier32
import InitECandidate.Runtime.HashTableSetNoGrowthOrder32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableArraysInvariant32.set_with_growth_frontier {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos items bits state)
    (entries : HashOrderEntriesBound order capacity items state)
    (allocated : orderPos.toNat + capacity.toNat * 8 ≤ pointer.toNat)
    (strideBound : stride.toNat ≤ 56) (pointerAligned : pointer.toNat % 8 = 0)
    (pointerBound : pointer.toNat ≤ 33806089496)
    (capacityBound : capacity.toNat ≤ 33806089496)
    (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (ticks : 2 * capacity.toNat + 2 * (capacity * 2).toNat + 44 + items.toNat * ((capacity * 2).toNat + 36) ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (capacityLarge : 1 < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set) =
        (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      ((∃ nextCount : BitVec 64, (nextCount = items ∨ nextCount = items + 1) ∧
        HashTableArraysInvariant32 table keys stride capacity used values order orderPos nextCount bits post ∧
        HashOrderEntriesBound order capacity nextCount post ∧
        HashTableHeapFrontier32 orderPos capacity pointer post) ∨
       (HashTableArraysInvariant32 table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
        (htabGrowOrderPos pointer capacity stride) (items + 1) (bits + 1) post ∧
        HashOrderEntriesBound (htabGrowOrder pointer capacity stride) (capacity * 2) (items + 1) post ∧
        HashTableHeapFrontier32 (htabGrowOrderPos pointer capacity stride) (capacity * 2)
          (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post)) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 2 * (capacity * 2).toNat + 44 + items.toNat * ((capacity * 2).toNat + 36) ∧
      post.clock ≤ state.clock ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  by_cases below : (items.toNat + 1) * 2 ≤ capacity.toNat
  · have doubled : (capacity * (2 : BitVec 64)).toNat = 2 * capacity.toNat := by
      rw [BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)]
      change capacity.toNat * 2 = 2 * capacity.toNat
      omega
    obtain ⟨nextCount,post,counts,run,valid,orderValid,cost,remaining,globals,code,addresses,endian⟩ :=
      invariant.set_no_growth_order state table keys stride capacity used values order orderPos items key value bits
        tableLocal keyLocal valueLocal keyAligned sourceWordDomain sourceByteDomain below (by rw [doubled] at ticks; omega) entries
    exact ⟨post,run,Or.inl ⟨nextCount,counts,valid,orderValid,
      (show HashTableHeapFrontier32 orderPos capacity pointer state from
        ⟨heap,allocated,pointerBound,pointerAligned⟩).after_globals state post _ _ _ globals⟩,by rw [doubled]; omega,remaining,code,addresses,endian⟩
  · obtain ⟨post,run,cases,cost,remaining,code,addresses,endian⟩ := invariant.set_above_threshold_frontier state
      table pointer keys stride capacity used values order orderPos items key value bits entries allocated strideBound pointerAligned
      pointerBound capacityBound safePlan ticks heap domain tableLocal keyLocal valueLocal (by omega) capacityLarge keyAligned sourceWordDomain sourceByteDomain
    refine ⟨post,run,?_,cost,remaining,code,addresses,endian⟩
    rcases cases with unchanged | grown
    · exact Or.inl ⟨items,Or.inl rfl,unchanged⟩
    · exact Or.inr grown

#print axioms HashTableArraysInvariant32.set_with_growth_frontier
end InitECandidate.Runtime
