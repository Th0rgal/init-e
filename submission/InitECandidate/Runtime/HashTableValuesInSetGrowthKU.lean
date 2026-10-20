import InitECandidate.Runtime.HashTableValuesInSetGrowth
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
/-! Unaligned-key copy of `HashTableValuesInSetGrowth` (generated; see PtKeyULeafKUGD): key alignment replaced by `key % 8 ≠ 0`, `8 ≤ keyLength`
and the key fit; lookup budgets made linear in the width bound (`54·cap`). -/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Registered values survive the actual missing-key growth branch, with its
rehash premises derived from the caller’s ready table invariant. -/
theorem HashTableReady.set_missing_growth_values_inKU {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (k : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (v : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (strideBound : stride.toNat ≤ 56) (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (ticks : 2 * (capacity * 2).toNat + keyLength.toNat + 10 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ≤ state.clock)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (above : capacity.toNat < (items.toNat + 1) * 2) (capacityLarge : 1 < capacity.toNat)
    (keyAligned : key.toNat % 8 ≠ 0) (len8 : 8 ≤ keyLength.toNat) (keyFit : key.toNat + keyLength.toNat ≤ 33806089496)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (targets : Set (BitVec 64)) (entries : HashTableValuesIn table targets state) (member : value ∈ targets) :
    ∃ post, evaluateHOLFiniteState state hashSetMissing =
        (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableReady keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
        (htabGrowOrderPos pointer capacity stride) (items + 1) (bits + 1)
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post ∧
      HashTableValuesIn table targets post ∧
      state.clock ≤ post.clock + 2 * (capacity * 2).toNat + keyLength.toNat + 10 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ∧
      post.clock ≤ state.clock ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have old := ready.live.arrays.old_arrays_width state keyLength table keys stride capacity used values order orderPos items bits pointer.toNat
    ready.live.entries ready.live.frontier.allocated (by have bound := ready.live.frontier.bounded; omega)
  have header : table.toNat + 72 ≤ pointer.toNat := by
    have before := old.headerOrder
    have allocated := old.orderEnd
    omega
  have u := ready.live.arrays.usedBefore
  have o := ready.live.arrays.orderBefore
  have vBefore := ready.live.arrays.valuesBefore
  have e := ready.live.arrays.endBound
  have allocated := ready.live.frontier.allocated
  have capBound : capacity.toNat ≤ 33806089496 := by omega
  have doubled : (capacity * (2 : BitVec 64)).toNat = capacity.toNat * 2 :=
    BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)
  have room := ready.live.arrays.room
  have oldRegistered := ready.order_values_in state keyLength table keys stride capacity used values order orderPos items pointer bits targets entries
  exact evaluate_hashSet_missing_growth_values_inKU state keyLength table pointer capacity stride keys values order items key value bits supported
    ready.live.arrays.code ready.live.arrays.power old ready.live.arrays.strideAligned ready.live.arrays.fits strideBound
    ready.live.frontier.aligned header ready.live.frontier.bounded capBound safePlan ticks ready.live.frontier.heap domain
    ready.live.arrays.cell0 ready.live.arrays.cell16 ready.live.arrays.cell8 ready.live.arrays.cell32 ready.live.arrays.cell40 ready.live.arrays.cell56 ready.live.arrays.cell24
    t k v
    (ready.live.arrays.header_domain state keyLength table keys stride capacity used values order orderPos items bits 16 (by decide))
    (ready.live.arrays.header_domain state keyLength table keys stride capacity used values order orderPos items bits 24 (by decide))
    above room (by rw [doubled]; omega) keyAligned len8 keyFit sourceWordDomain sourceByteDomain
    targets ready.live.arrays.headerValues (by omega) oldRegistered member

#print axioms HashTableReady.set_missing_growth_values_inKU
end InitECandidate.Runtime
