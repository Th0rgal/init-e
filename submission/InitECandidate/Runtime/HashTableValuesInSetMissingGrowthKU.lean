import InitECandidate.Runtime.HashTableValuesInSetMissingGrowth
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
/-! Unaligned-key copy of `HashTableValuesInSetMissingGrowth` (generated; see PtKeyULeafKUGD): key alignment replaced by `key % 8 ≠ 0`, `8 ≤ keyLength`
and the key fit; lookup budgets made linear in the width bound (`54·cap`). -/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual missing-key growth branch retains registered values through
successful growth, insertion of a registered value, and its final return. -/
theorem evaluate_hashSet_missing_growth_values_inKU {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (keyAligned : key.toNat % 8 ≠ 0) (len8 : 8 ≤ keyLength.toNat) (keyFit : key.toNat + keyLength.toNat ≤ 33806089496)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (targets : Set (BitVec 64)) (headerValues : table.toNat + 72 ≤ values.toNat)
    (valuesEnd : values.toNat + capacity.toNat * 8 ≤ pointer.toNat)
    (oldRegistered : HashOrderValuesIn order values items targets state) (member : value ∈ targets) :
    ∃ post, evaluateHOLFiniteState state hashSetMissing =
        (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableReady keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
        (htabGrowOrderPos pointer capacity stride) (items + 1) (bits + 1)
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post ∧
      HashTableValuesIn table targets post ∧
      state.clock ≤ post.clock + 2 * (capacity * 2).toNat + keyLength.toNat + 10 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ∧
      post.clock ≤ state.clock ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.var .local (ofString "t")] = some [.val (.word table)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,tableLocal]
  obtain ⟨grown,growRun,grownReady,_,grownRegistered,_,cost,remaining,locals,growCode,addresses,endian,_⟩ :=
    evaluate_htabGrow_ready_values_in state keyLength table pointer capacity stride keys values order items bits supported
      (.var .local (ofString "t")) arguments code power old strideAligned fits strideBound pointerAligned headerBefore pointerBound capacityBound safePlan
      (by omega) heap domain keyField cell16 cell8 cell32 cell40 cell56 cell24 targets headerValues valuesEnd oldRegistered
  have insertArgs : evalListHOLFinite grown
      (h := fun address => Classical.propDecidable (grown.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")] =
      some [.val (.word table),.val (.word key),.val (.word value)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,locals,tableLocal,keyLocal,valueLocal]
  have words : ∀ offset : Nat, offset < keyLength.toNat → grown.memaddrs (key + BitVec.ofNat 64 offset) := by
    rw [addresses]; exact sourceWordDomain
  have bytes : ∀ offset : Nat, offset < keyLength.toNat → grown.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)) := by
    rw [addresses]; exact sourceByteDomain
  obtain ⟨inserted,insertRun,finalReady,insertRegistered,_,insertCost,insertRemaining,_,_,finalAddresses,finalEndian⟩ :=
    grownReady.insert_supported_values_in_frameKU grown keyLength table
      (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8))
      pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
      (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride)
      items key value (bits + 1) supported _ _ _ insertArgs keyAligned len8 keyFit words bytes roomAfter (by omega) targets grownRegistered member
  have selected := evaluate_hashSet_growth_selected state table capacity items tableLocal domain16 cell16 domain24 cell24
    loadFactor room (by omega)
  have returned : evaluateHOLFiniteState inserted (.return (.const 0)) =
      (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite inserted) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  refine ⟨emptyLocalsHOLFinite inserted,?_,
    HashTableReady.after_read inserted _ keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
      (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride)
      (items + 1) (bits + 1) (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8))
      finalReady rfl rfl rfl rfl rfl,
    insertRegistered.after_read rfl rfl rfl,(by change state.clock ≤ inserted.clock + 2 * (capacity * 2).toNat + keyLength.toNat + 10 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4); omega),
    (by change inserted.clock ≤ state.clock; omega),?_,finalAddresses.trans addresses,finalEndian.trans endian⟩
  · rw [source_hashSet_missing]
    exact evaluate_seq_none (selected.trans growRun) (evaluate_seq_none insertRun returned)
  · exact finalReady.live.arrays.code.trans code.symm

#print axioms evaluate_hashSet_missing_growth_values_inKU
end InitECandidate.Runtime
