import InitECandidate.Runtime.HashTableValuesInSetCallAllPlans
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
import InitECandidate.Runtime.HashTableSetLookupFailureTerminalSupportedNoTimeoutKU
import InitECandidate.Runtime.HashTableValuesInInsertCopyKU
import InitECandidate.Runtime.HashTableValuesInInsertProbeKU
import InitECandidate.Runtime.HashTableValuesInInsertCallKU
import InitECandidate.Runtime.HashTableValuesInReadyUpdatesKU
import InitECandidate.Runtime.HashTableValuesInSetMissingGrowthKU
import InitECandidate.Runtime.HashTableValuesInSetGrowthKU
import InitECandidate.Runtime.HashTableValuesInSetAboveThresholdKU
import InitECandidate.Runtime.HashTableValuesInSetMissingKU
import InitECandidate.Runtime.HashTableValuesInSetNoGrowthKU
import InitECandidate.Runtime.HashTableValuesInSetSafePlanKU
import InitECandidate.Runtime.HashTableValuesInSetCallNoGrowthKU
import InitECandidate.Runtime.HashTableValuesInSetCallSafePlanKU
import InitECandidate.Runtime.HashTableValuesInSetCallUniformKU
import InitECandidate.Runtime.HashTableValuesInSetExistingLookupKU
import InitECandidate.Runtime.HashTableValuesInSetUnsafeKU
import InitECandidate.Runtime.HashTableValuesInSetCallUnsafeKU
/-! Unaligned-key copy of `HashTableValuesInSetCallAllPlans` (generated; see PtKeyULeafKUGD): key alignment replaced by `key % 8 ≠ 0`, `8 ≤ keyLength`
and the key fit; lookup budgets made linear in the width bound (`54·cap`). -/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableReady.set_call_all_plans_values_inKU {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (initialReady : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn table targets state) (member : value ∈ targets)
    (strideBound : stride.toNat ≤ 56)
    (ticks : 2 ^ 74 ≤ state.clock)
    (domain : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride) → ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (capacityLarge : 1 < capacity.toNat)
    (keyAligned : key.toNat % 8 ≠ 0) (len8 : 8 ≤ keyLength.toNat) (keyFit : key.toNat + keyLength.toNat ≤ 33806089496)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    (∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set")
        [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      ((∃ nextCount : BitVec 64, (nextCount = items ∨ nextCount = items + 1) ∧
        HashTableReady keyLength table keys stride capacity used values order orderPos nextCount bits pointer post) ∨
       HashTableReady keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
        (htabGrowOrderPos pointer capacity stride) (items + 1) (bits + 1)
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post ) ∧
      HashTableValuesIn table targets post ∧
      state.clock ≤ post.clock + 2 ^ 74 ∧
      post.clock ≤ state.clock ∧ post.locals = state.locals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be) ∨
    ((evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).1 ≠ none ∧
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).1 ≠ some .timeOut ∧
    (∀ output : ValueHOL 64, (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).1 ≠ some (.returned output)) ∧
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).1 ≠ some .continue ∧
    state.clock ≤ (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).2.clock + 2 ^ 74 ∧
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).2.clock ≤ state.clock) := by
  have u := initialReady.live.arrays.usedBefore
  have o := initialReady.live.arrays.orderBefore
  have e := initialReady.live.arrays.endBound
  have capBound : capacity.toNat ≤ 33806089496 := by omega
  have keyBound : keyLength.toNat ≤ 52 := by rcases supported with h | h | h <;> simp [h]
  by_cases below : (items.toNat + 1) * 2 ≤ capacity.toNat
  · obtain ⟨nextCount,post,counts,run,valid,postRegistered,_,cost,remaining,locals,_,code,addresses,endian⟩ :=
      initialReady.set_call_no_growth_values_inKU state keyLength table pointer keys stride capacity used values order orderPos items key value bits supported
        keyAligned len8 keyFit sourceWordDomain sourceByteDomain below (by omega) tableArgument keyArgument valueArgument arguments targets registered member
    exact Or.inl ⟨post,run,Or.inl ⟨nextCount,counts,valid⟩,postRegistered,by omega,remaining,locals,code,addresses,endian⟩
  · by_cases safe : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride)
    · exact Or.inl (initialReady.set_call_safe_plan_values_in_uniformKU state keyLength table pointer keys stride capacity used values order orderPos items key value bits supported
        targets registered member strideBound safe ticks (domain safe) tableArgument keyArgument valueArgument arguments capacityLarge keyAligned len8 keyFit sourceWordDomain sourceByteDomain)
    · have outcome := initialReady.set_unsafe_growth_call_values_in_dichotomyKU state keyLength table pointer keys stride capacity used values order orderPos items key value bits supported
        targets registered member tableArgument keyArgument valueArgument arguments keyAligned len8 keyFit sourceWordDomain sourceByteDomain (by omega)
        initialReady.live.frontier.heap initialReady.live.frontier.bounded safe (by omega)
      rcases outcome with success | failure
      · obtain ⟨post,run,valid,postRegistered,locals,code,addresses,endian,cost,remaining⟩ := success
        exact Or.inl ⟨post,run,Or.inl ⟨items,Or.inl rfl,valid⟩,postRegistered,by omega,remaining,locals,code,addresses,endian⟩
      · obtain ⟨terminal,noTimeout,noReturn,noContinue,cost,remaining⟩ := failure
        exact Or.inr ⟨terminal,noTimeout,noReturn,noContinue,by omega,remaining⟩

#print axioms HashTableReady.set_call_all_plans_values_inKU
end InitECandidate.Runtime
