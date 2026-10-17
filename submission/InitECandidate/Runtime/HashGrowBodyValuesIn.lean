import InitECandidate.Runtime.HashGrowBodySafePlanSupported
import InitECandidate.Runtime.HashGrowRehashScopeValuesIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete successful original growth body preserves registered values.
The allocation/header-reset prefix protects the old order/value arrays and
establishes an empty new table before the checked rehash loop. -/
theorem evaluate_source_htabGrow_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer capacity stride keys values order items : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (code : state.code = originalRuntimeCode) (power : capacity.toNat = 2 ^ bits)
    (old : HashGrowOldArrays table keys stride values order capacity items pointer.toNat state)
    (strideAligned : stride.toNat % 8 = 0) (fits : keyLength.toNat ≤ stride.toNat) (strideBound : stride.toNat ≤ 56)
    (pointerAligned : pointer.toNat % 8 = 0) (headerBefore : table.toNat + 72 ≤ pointer.toNat)
    (pointerBound : pointer.toNat ≤ 33806089496)
    (capacityBound : capacity.toNat ≤ 33806089496)
    (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (ticks : (capacity * 2).toNat + 6 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyField : state.memory (table + 0) = .word keyLength)
    (cell16 : state.memory (table + 16) = .word capacity)
    (cell8 : state.memory (table + 8) = .word stride)
    (cell32 : state.memory (table + 32) = .word keys)
    (cell40 : state.memory (table + 40) = .word values)
    (cell56 : state.memory (table + 56) = .word order)
    (cell24 : state.memory (table + 24) = .word items)
    (targets : Set (BitVec 64)) (headerValues : table.toNat + 72 ≤ values.toNat)
    (valuesEnd : values.toNat + capacity.toNat * 8 ≤ pointer.toNat)
    (oldRegistered : HashOrderValuesIn order values items targets state) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_grow) =
        (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableArraysInvariant keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
        (htabGrowOrderPos pointer capacity stride) items (bits + 1) post ∧
      HashOrderEntriesBound (htabGrowOrder pointer capacity stride) (capacity * 2) items post ∧
      HashValueEntriesWord (htabGrowUsed pointer capacity stride) (htabGrowValues pointer capacity stride) (capacity * 2) post ∧
      HashReverseEntriesBound (htabGrowUsed pointer capacity stride) (htabGrowOrderPos pointer capacity stride) (capacity * 2) items post ∧
      HashOrderLinked (htabGrowUsed pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride) (capacity * 2) items post ∧
      HashGrowOldArrays table keys stride values order capacity items pointer.toNat post ∧
      HashTableValuesIn table targets post ∧ HashOrderValuesIn order values items targets post ∧
      state.clock ≤ post.clock + (capacity * 2).toNat + 6 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ∧
      post.clock ≤ state.clock ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ watched : BitVec 64, table.toNat + 72 ≤ watched.toNat → watched.toNat < pointer.toNat →
        post.memory watched = state.memory watched) := by
  obtain ⟨ready,prefixRun,valid,cost,remaining,postCode,addresses,endian,t,k,s,v,o,n,_,prefixFrame⟩ :=
    evaluate_htabGrow_prefix_width_safe_plan state keyLength table pointer capacity stride keys values order items bits hashGrowRehashScope code power
      strideAligned fits strideBound pointerAligned headerBefore pointerBound capacityBound safePlan (by omega) heap domain tableLocal keyField cell16 cell8 cell32 cell40 cell56 cell24
  have oldReady := old.preserved state ready table keys stride values order capacity items pointer.toNat addresses prefixFrame
  have oldRegisteredReady := oldRegistered.preserved state ready table keys stride values order capacity items pointer.toNat old targets
    headerValues valuesEnd prefixFrame
  have doubled : (capacity * (2 : BitVec 64)).toNat = 2 * capacity.toNat := by
    rw [BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)]
    change capacity.toNat * 2 = 2 * capacity.toNat
    omega
  have keyValueOrder := htabGrow_keys_before_values pointer capacity stride pointerBound capacityBound strideBound safePlan
  have safe := safePlan
  obtain ⟨guard,_,_⟩ := safe
  have lower := (allocationEnd_covers pointer ((capacity * 2) * stride)
    (allocationGuard_sum_bound pointer _ (by omega) guard)).1
  have beforeValues : pointer.toNat ≤ (htabGrowValues pointer capacity stride).toNat := by
    change pointer.toNat ≤ (allocationEnd pointer ((capacity * 2) * stride)).toNat
    omega
  have positive : 0 < capacity.toNat := by rw [power]; exact Nat.two_pow_pos bits
  have fitItems : items.toNat < (capacity * 2).toNat := by
    rw [doubled]
    have bound := old.itemsBound
    omega
  obtain ⟨post,rehash,postValid,postEntries,postValues,postReverse,postLinked,postOld,registeredPost,oldRegisteredPost,rehashCost,rehashRemaining,_,lastCode,lastAddresses,lastEndian,rehashFrame⟩ :=
    evaluate_hashGrow_rehash_scope_values_in ready keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
      (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride)
      keys values order capacity items (bits + 1) pointer.toNat supported valid oldReady (Nat.le_refl _) beforeValues fitItems keyValueOrder
      t k s v o n (by omega) targets headerValues valuesEnd oldRegisteredReady
  rw [source_htabGrow_header_prefix]
  change ∃ post, evaluateHOLFiniteState state (hashGrowHeaderLoads (hashGrowKeysAllocation hashGrowRehashScope)) = _ ∧ _
  rw [prefixRun,rehash]
  refine ⟨_,rfl,postValid.after_read post _ keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
      (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride)
      items (bits + 1) rfl rfl rfl rfl,
    postEntries.after_memory post _ (htabGrowOrder pointer capacity stride) (capacity * 2) items rfl,
    postValues.after_read post _ (htabGrowUsed pointer capacity stride) (htabGrowValues pointer capacity stride) (capacity * 2) rfl rfl rfl,
    postReverse.after_read post _ (htabGrowUsed pointer capacity stride) (htabGrowOrderPos pointer capacity stride) (capacity * 2) items rfl rfl rfl,
    postLinked.after_read post _ (htabGrowUsed pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride) (capacity * 2) items rfl rfl rfl,
    postOld.preserved post _ table keys stride values order capacity items pointer.toNat rfl (by intro watched lower upper; rfl),
    registeredPost.after_read rfl rfl rfl,oldRegisteredPost.after_memory rfl,?_,?_,lastCode.trans postCode,lastAddresses.trans addresses,lastEndian.trans endian,?_⟩
  · change state.clock ≤ post.clock + (capacity * 2).toNat + 6 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4)
    omega
  · change post.clock ≤ state.clock
    omega
  · intro watched lower upper
    exact (rehashFrame watched lower upper).trans (prefixFrame watched lower upper)

#print axioms evaluate_source_htabGrow_values_in
end InitECandidate.Runtime
