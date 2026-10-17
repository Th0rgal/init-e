import InitECandidate.Runtime.HashGrowCallSafePlanSupported
import InitECandidate.Runtime.HashSetGrowthTrue
import InitECandidate.Runtime.HashTableArraysLinkedInsertSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashSet_missing_growth_supported_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer capacity stride keys values order items key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (code : state.code = originalRuntimeCode) (power : capacity.toNat = 2 ^ bits)
    (old : HashGrowOldArrays table keys stride values order capacity items pointer.toNat state)
    (strideAligned : stride.toNat % 8 = 0) (fits : keyLength.toNat ≤ stride.toNat) (strideBound : stride.toNat ≤ 56)
    (pointerAligned : pointer.toNat % 8 = 0) (headerBefore : table.toNat + 72 ≤ pointer.toNat)
    (pointerBound : pointer.toNat ≤ 33806089496)
    (capacityBound : capacity.toNat ≤ 33806089496)
    (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (ticks : 2 * (capacity * 2).toNat + keyLength.toNat + 10 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (keyField : state.memory (table + 0) = .word keyLength)
    (cell16 : state.memory (table + 16) = .word capacity)
    (cell8 : state.memory (table + 8) = .word stride)
    (cell32 : state.memory (table + 32) = .word keys)
    (cell40 : state.memory (table + 40) = .word values)
    (cell56 : state.memory (table + 56) = .word order)
    (cell24 : state.memory (table + 24) = .word items)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (domain16 : state.memaddrs (table + 16)) (domain24 : state.memaddrs (table + 24))
    (loadFactor : capacity.toNat < (items.toNat + 1) * 2)
    (room : items.toNat < capacity.toNat)
    (roomAfter : items.toNat + 1 < (capacity * 2).toNat)
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state hashSetMissing =
        (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableArraysInvariant keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
        (htabGrowOrderPos pointer capacity stride) (items + 1) (bits + 1) post ∧
      HashOrderEntriesBound (htabGrowOrder pointer capacity stride) (capacity * 2) (items + 1) post ∧
      HashValueEntriesWord (htabGrowUsed pointer capacity stride) (htabGrowValues pointer capacity stride) (capacity * 2) post ∧
      HashReverseEntriesBound (htabGrowUsed pointer capacity stride) (htabGrowOrderPos pointer capacity stride) (capacity * 2) (items + 1) post ∧
      HashOrderLinked (htabGrowUsed pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride) (capacity * 2) (items + 1) post ∧
      state.clock ≤ post.clock + 2 * (capacity * 2).toNat + keyLength.toNat + 10 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ∧
      post.clock ≤ state.clock ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.var .local (ofString "t")] = some [.val (.word table)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,tableLocal]
  obtain ⟨grown,growRun,valid,entries,valueEntries,reverseEntries,grownLinked,_,cost,remaining,locals,growCode,addresses,endian,_⟩ :=
    evaluate_htabGrow_supported_call_safe_plan state keyLength table pointer capacity stride keys values order items bits supported
      (.var .local (ofString "t")) arguments code power old strideAligned fits strideBound pointerAligned headerBefore pointerBound capacityBound safePlan
      (by omega) heap domain keyField cell16 cell8 cell32 cell40 cell56 cell24
  have insertArgs : evalListHOLFinite grown
      (h := fun address => Classical.propDecidable (grown.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")] =
      some [.val (.word table),.val (.word key),.val (.word value)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,locals,tableLocal,keyLocal,valueLocal]
  have words : ∀ offset : Nat, offset < keyLength.toNat → grown.memaddrs (key + BitVec.ofNat 64 offset) := by
    rw [addresses]; exact sourceWordDomain
  have bytes : ∀ offset : Nat, offset < keyLength.toNat → grown.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)) := by
    rw [addresses]; exact sourceByteDomain
  obtain ⟨inserted,insertRun,finalValid,finalEntries,finalValues,finalReverse,finalLinked,insertCost,insertRemaining,_,_,finalAddresses,finalEndian⟩ :=
    valid.insert_supported_all_entries_linked grown keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
      (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride)
      items key value (bits + 1) supported _ _ _ insertArgs keyAligned words bytes roomAfter (by omega) entries valueEntries reverseEntries grownLinked
      (htabGrow_keys_before_values pointer capacity stride pointerBound capacityBound strideBound safePlan)
  have selected := evaluate_hashSet_growth_selected state table capacity items tableLocal domain16 cell16 domain24 cell24
    loadFactor room (by omega)
  have returned : evaluateHOLFiniteState inserted (.return (.const 0)) =
      (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite inserted) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  refine ⟨emptyLocalsHOLFinite inserted,?_,
    finalValid.after_read inserted _ keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
      (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride)
      (items + 1) (bits + 1) rfl rfl rfl rfl,
    finalEntries.after_memory inserted _ _ _ _ rfl,
    finalValues.after_read inserted _ _ _ _ rfl rfl rfl,
    finalReverse.after_read inserted _ _ _ _ _ rfl rfl rfl,
    finalLinked.after_read inserted _ _ _ _ _ _ rfl rfl rfl,(by change state.clock ≤ inserted.clock + 2 * (capacity * 2).toNat + keyLength.toNat + 10 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4); omega),(by change inserted.clock ≤ state.clock; omega),?_,finalAddresses.trans addresses,finalEndian.trans endian⟩
  · rw [source_hashSet_missing]
    exact evaluate_seq_none (selected.trans growRun) (evaluate_seq_none insertRun returned)
  · exact finalValid.code.trans code.symm

#print axioms evaluate_hashSet_missing_growth_supported_safe_plan
end InitECandidate.Runtime
