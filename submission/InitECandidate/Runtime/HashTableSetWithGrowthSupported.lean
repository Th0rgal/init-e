import InitECandidate.Runtime.HashTableSetAboveThresholdSupported
import InitECandidate.Runtime.HashTableSetNoGrowthSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableArraysInvariant.set_with_growth_supported_safe_plan {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
    (entries : HashOrderEntriesBound order capacity items state)
    (valueEntries : HashValueEntriesWord used values capacity state)
    (reverseEntries : HashReverseEntriesBound used orderPos capacity items state)
    (linked : HashOrderLinked used order orderPos capacity items state)
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (allocated : orderPos.toNat + capacity.toNat * 8 ≤ pointer.toNat)
    (strideBound : stride.toNat ≤ 56) (pointerAligned : pointer.toNat % 8 = 0)
    (pointerBound : pointer.toNat ≤ 33806089496)
    (capacityBound : capacity.toNat ≤ 33806089496)
    (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (ticks : 2 * capacity.toNat + 2 * (capacity * 2).toNat + keyLength.toNat + 12 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (capacityLarge : 1 < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set) =
        (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      ((∃ nextCount : BitVec 64, (nextCount = items ∨ nextCount = items + 1) ∧
        HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos nextCount bits post ∧
        HashOrderEntriesBound order capacity nextCount post ∧
        HashValueEntriesWord used values capacity post ∧ HashReverseEntriesBound used orderPos capacity nextCount post ∧
        HashOrderLinked used order orderPos capacity nextCount post) ∨
       (HashTableArraysInvariant keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
        (htabGrowOrderPos pointer capacity stride) (items + 1) (bits + 1) post ∧
        HashOrderEntriesBound (htabGrowOrder pointer capacity stride) (capacity * 2) (items + 1) post ∧
        HashValueEntriesWord (htabGrowUsed pointer capacity stride) (htabGrowValues pointer capacity stride) (capacity * 2) post ∧
        HashReverseEntriesBound (htabGrowUsed pointer capacity stride) (htabGrowOrderPos pointer capacity stride) (capacity * 2) (items + 1) post ∧
        HashOrderLinked (htabGrowUsed pointer capacity stride) (htabGrowOrder pointer capacity stride)
          (htabGrowOrderPos pointer capacity stride) (capacity * 2) (items + 1) post)) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 2 * (capacity * 2).toNat + keyLength.toNat + 12 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ∧
      post.clock ≤ state.clock ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  by_cases below : (items.toNat + 1) * 2 ≤ capacity.toNat
  · have doubled : (capacity * (2 : BitVec 64)).toNat = 2 * capacity.toNat := by
      rw [BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)]
      change capacity.toNat * 2 = 2 * capacity.toNat
      omega
    obtain ⟨nextCount,post,counts,run,valid,words,reverse,orderValid,postLinked,cost,remaining,_,code,addresses,endian⟩ :=
      invariant.set_no_growth_supported state keyLength table keys stride capacity used values order orderPos items key value bits supported
        tableLocal keyLocal valueLocal keyAligned sourceWordDomain sourceByteDomain below (by rw [doubled] at ticks; omega) valueEntries reverseEntries entries linked keysBeforeValues
    exact ⟨post,run,Or.inl ⟨nextCount,counts,valid,orderValid,words,reverse,postLinked⟩,by rw [doubled]; omega,remaining,code,addresses,endian⟩
  · obtain ⟨post,run,cases,cost,remaining,code,addresses,endian⟩ := invariant.set_above_threshold_supported_safe_plan state
      keyLength table pointer keys stride capacity used values order orderPos items key value bits supported entries valueEntries reverseEntries linked allocated strideBound pointerAligned
      pointerBound capacityBound safePlan ticks heap domain tableLocal keyLocal valueLocal (by omega) capacityLarge keyAligned sourceWordDomain sourceByteDomain
    refine ⟨post,run,?_,cost,remaining,code,addresses,endian⟩
    rcases cases with unchanged | grown
    · exact Or.inl ⟨items,Or.inl rfl,unchanged⟩
    · exact Or.inr grown

#print axioms HashTableArraysInvariant.set_with_growth_supported_safe_plan
end InitECandidate.Runtime
