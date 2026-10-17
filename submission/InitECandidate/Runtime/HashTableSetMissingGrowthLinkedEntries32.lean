import InitECandidate.Runtime.HashSetMissingGrowthSafePlanLinkedEntries32
import InitECandidate.Runtime.HashTableGrowOldArrays32
import InitECandidate.Runtime.HashTableArraysFind32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableArraysInvariant32.set_missing_growth_safe_plan_linked_entries {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos items bits state)
    (entries : HashOrderEntriesBound order capacity items state)
    (allocated : orderPos.toNat + capacity.toNat * 8 ≤ pointer.toNat)
    (strideBound : stride.toNat ≤ 56) (pointerAligned : pointer.toNat % 8 = 0)
    (pointerBound : pointer.toNat ≤ 33806089496)
    (capacityBound : capacity.toNat ≤ 33806089496)
    (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (ticks : 2 * (capacity * 2).toNat + 42 + items.toNat * ((capacity * 2).toNat + 36) ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (loadFactor : capacity.toNat < (items.toNat + 1) * 2)
    (capacityLarge : 1 < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state hashSetMissing =
        (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableArraysInvariant32 table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
        (htabGrowOrderPos pointer capacity stride) (items + 1) (bits + 1) post ∧
      HashOrderEntriesBound (htabGrowOrder pointer capacity stride) (capacity * 2) (items + 1) post ∧
      HashValueEntriesWord (htabGrowUsed pointer capacity stride) (htabGrowValues pointer capacity stride) (capacity * 2) post ∧
      HashReverseEntriesBound (htabGrowUsed pointer capacity stride) (htabGrowOrderPos pointer capacity stride) (capacity * 2) (items + 1) post ∧
      HashOrderLinked (htabGrowUsed pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride) (capacity * 2) (items + 1) post ∧
      state.clock ≤ post.clock + 2 * (capacity * 2).toNat + 42 + items.toNat * ((capacity * 2).toNat + 36) ∧
      post.clock ≤ state.clock ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have old := invariant.old_arrays state table keys stride capacity used values order orderPos items bits pointer.toNat entries allocated (by omega)
  have header : table.toNat + 72 ≤ pointer.toNat := by
    have := old.headerOrder
    have := old.orderEnd
    omega
  have doubled : (capacity * (2 : BitVec 64)).toNat = 2 * capacity.toNat := by
    rw [BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)]
    change capacity.toNat * 2 = 2 * capacity.toNat
    omega
  have roomAfter : items.toNat + 1 < (capacity * 2).toNat := by
    rw [doubled]
    have := invariant.room
    omega
  exact evaluate_hashSet_missing_growth32_safe_plan_linked_entries state table pointer capacity stride keys values order items key value bits
    invariant.code invariant.power old invariant.strideAligned invariant.fits strideBound pointerAligned header pointerBound capacityBound safePlan ticks heap domain
    invariant.cell0 invariant.cell16 invariant.cell8 invariant.cell32 invariant.cell40 invariant.cell56 invariant.cell24
    tableLocal keyLocal valueLocal
    (invariant.header_domain state table keys stride capacity used values order orderPos items bits 16 (by decide))
    (invariant.header_domain state table keys stride capacity used values order orderPos items bits 24 (by decide))
    loadFactor invariant.room roomAfter keyAligned sourceWordDomain sourceByteDomain

#print axioms HashTableArraysInvariant32.set_missing_growth_safe_plan_linked_entries
end InitECandidate.Runtime
