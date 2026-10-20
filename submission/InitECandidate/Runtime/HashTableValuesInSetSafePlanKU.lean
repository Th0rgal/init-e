import InitECandidate.Runtime.HashTableValuesInSetSafePlan
import InitECandidate.Runtime.PtKeyULeafKUGD
import InitECandidate.Runtime.HashInsertProbeTailKU
import InitECandidate.Runtime.HashInsertCopyMemoryKU
import InitECandidate.Runtime.HashInsertCopyOrderedMemoryKU
import InitECandidate.Runtime.HashInsertProbeMemoryKU
import InitECandidate.Runtime.HashInsertCopyBoundsKU
import InitECandidate.Runtime.HashInsertProbeArraysMemoryKU
import InitECandidate.Runtime.HashInsertIndexMemoryKU
import InitECandidate.Runtime.HashInsertCopyOrderEntriesKU
import InitECandidate.Runtime.HashInsertCopyOrderedEntriesKU
import InitECandidate.Runtime.HashInsertCopyEntriesKU
import InitECandidate.Runtime.HashInsertCopyEntriesWidthKU
import InitECandidate.Runtime.HashInsertProbeEntriesWidthKU
import InitECandidate.Runtime.HashInsertIndexEntriesWidthKU
import InitECandidate.Runtime.HashInsertHashAllEntriesSupportedKU
import InitECandidate.Runtime.HashInsertBodyAllEntriesSupportedKU
import InitECandidate.Runtime.HashInsertCopyLinkedWidthKU
import InitECandidate.Runtime.HashInsertProbeLinkedWidthKU
import InitECandidate.Runtime.HashInsertIndexLinkedWidthKU
import InitECandidate.Runtime.HashInsertHashLinkedSupportedKU
import InitECandidate.Runtime.HashInsertBodyLinkedSupportedKU
import InitECandidate.Runtime.HashInsertHashMemorySupportedKU
import InitECandidate.Runtime.HashInsertBodyMemorySupportedKU
import InitECandidate.Runtime.HashInsertCallAllEntriesSupportedKU
import InitECandidate.Runtime.HashInsertCallLinkedSupportedKU
import InitECandidate.Runtime.HashInsertCallMemorySupportedKU
import InitECandidate.Runtime.HashTableArraysFrameSupportedKU
import InitECandidate.Runtime.HashTableArraysAllEntriesSupportedKU
import InitECandidate.Runtime.HashTableArraysLinkedInsertSupportedKU
import InitECandidate.Runtime.HashTableReadyInsertSupportedKU
import InitECandidate.Runtime.HashTableReadyInsertPhysicalFrameSupportedKU
import InitECandidate.Runtime.HashTableValuesInInsertCopyKU
import InitECandidate.Runtime.HashTableValuesInInsertProbeKU
import InitECandidate.Runtime.HashTableValuesInInsertCallKU
import InitECandidate.Runtime.HashTableValuesInReadyUpdatesKU
import InitECandidate.Runtime.HashTableValuesInSetMissingGrowthKU
import InitECandidate.Runtime.HashTableValuesInSetGrowthKU
import InitECandidate.Runtime.HashTableValuesInSetAboveThresholdKU
import InitECandidate.Runtime.HashTableValuesInSetMissingKU
import InitECandidate.Runtime.HashTableValuesInSetNoGrowthKU
/-! Unaligned-key copy of `HashTableValuesInSetSafePlan` (generated; see PtKeyULeafKUGD): key alignment replaced by `key % 8 ≠ 0`, `8 ≤ keyLength`
and the key fit; lookup budgets made linear in the width bound (`54·cap`). -/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableReady.set_safe_plan_values_inKU {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (initialReady : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn table targets state) (member : value ∈ targets)
    (strideBound : stride.toNat ≤ 56)
    (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (ticks : 54 * capacity.toNat + 2 * (capacity * 2).toNat + keyLength.toNat + 12 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ≤ state.clock)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (capacityLarge : 1 < capacity.toNat)
    (keyAligned : key.toNat % 8 ≠ 0) (len8 : 8 ≤ keyLength.toNat) (keyFit : key.toNat + keyLength.toNat ≤ 33806089496)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set) =
        (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      ((∃ nextCount : BitVec 64, (nextCount = items ∨ nextCount = items + 1) ∧
        HashTableReady keyLength table keys stride capacity used values order orderPos nextCount bits pointer post) ∨
       HashTableReady keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
        (htabGrowOrderPos pointer capacity stride) (items + 1) (bits + 1)
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post ) ∧
      HashTableValuesIn table targets post ∧
      state.clock ≤ post.clock + 54 * capacity.toNat + 2 * (capacity * 2).toNat + keyLength.toNat + 12 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ∧
      post.clock ≤ state.clock ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  by_cases below : (items.toNat + 1) * 2 ≤ capacity.toNat
  · have u := initialReady.live.arrays.usedBefore
    have o := initialReady.live.arrays.orderBefore
    have e := initialReady.live.arrays.endBound
    have capBound : capacity.toNat ≤ 33806089496 := by omega
    have doubled : (capacity * (2 : BitVec 64)).toNat = 2 * capacity.toNat := by
      rw [BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)]
      change capacity.toNat * 2 = 2 * capacity.toNat
      omega
    obtain ⟨nextCount,post,counts,run,valid,postRegistered,_,cost,remaining,_,code,addresses,endian⟩ :=
      initialReady.set_no_growth_values_inKU state keyLength table pointer keys stride capacity used values order orderPos items key value bits supported
        tableLocal keyLocal valueLocal keyAligned len8 keyFit sourceWordDomain sourceByteDomain below (by rw [doubled] at ticks; omega) targets registered member
    exact ⟨post,run,Or.inl ⟨nextCount,counts,valid⟩,postRegistered,by rw [doubled]; omega,remaining,code,addresses,endian⟩
  · obtain ⟨post,run,cases,postRegistered,cost,remaining,code,addresses,endian⟩ :=
      initialReady.set_above_threshold_values_inKU state keyLength table pointer keys stride capacity used values order orderPos items key value bits supported
        targets registered member strideBound safePlan ticks domain tableLocal keyLocal valueLocal (by omega) capacityLarge keyAligned len8 keyFit sourceWordDomain sourceByteDomain
    refine ⟨post,run,?_,postRegistered,cost,remaining,code,addresses,endian⟩
    rcases cases with unchanged | grown
    · exact Or.inl ⟨items,Or.inl rfl,unchanged⟩
    · exact Or.inr grown

#print axioms HashTableReady.set_safe_plan_values_inKU
end InitECandidate.Runtime
