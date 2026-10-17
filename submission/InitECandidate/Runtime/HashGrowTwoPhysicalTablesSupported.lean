import InitECandidate.Runtime.HashGrowPhysicalTableSupported
import InitECandidate.Runtime.HashGrowReadySupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_htabGrow_supported_two_physical_tables {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer capacity stride keys values order items : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (tableArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [tableArgument] = some [.val (.word table)])
    (code : state.code = originalRuntimeCode) (power : capacity.toNat = 2 ^ bits)
    (old : HashGrowOldArrays table keys stride values order capacity items pointer.toNat state)
    (strideAligned : stride.toNat % 8 = 0) (fits : keyLength.toNat ≤ stride.toNat) (strideBound : stride.toNat ≤ 56)
    (pointerAligned : pointer.toNat % 8 = 0) (headerBefore : table.toNat + 72 ≤ pointer.toNat)
    (pointerBound : pointer.toNat ≤ 33806089496)
    (capacityBound : capacity.toNat ≤ 33806089496)
    (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (ticks : (capacity * 2).toNat + 7 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ≤ state.clock)
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
    (otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64)
    (otherBits : Nat)
    (otherReady : HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (separate : ∀ address : BitVec 64, table.toNat ≤ address.toNat → address.toNat < table.toNat + 72 →
      ¬tablePhysicalRegion otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos address) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_grow") [tableArgument]) = (none,post) ∧
      HashTableReady keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride) items (bits + 1)
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post ∧
      HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post ∧
      state.clock ≤ post.clock + (capacity * 2).toNat + 7 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ∧
      post.clock ≤ state.clock ∧ post.locals = state.locals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨post,run,otherValid,cost,remaining,locals,postCode,postDomain,endian⟩ :=
    evaluate_htabGrow_supported_preserves_physical_table state keyLength table pointer capacity stride keys values order items bits supported tableArgument arguments code power old
      strideAligned fits strideBound pointerAligned headerBefore pointerBound capacityBound safePlan ticks heap domain
      keyField cell16 cell8 cell32 cell40 cell56 cell24
      otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherReady separate
  obtain ⟨checked,checkedRun,valid,_⟩ := evaluate_htabGrow_supported_ready state keyLength table pointer capacity stride keys values order items bits supported tableArgument arguments code power old
      strideAligned fits strideBound pointerAligned headerBefore pointerBound capacityBound safePlan ticks heap domain
      keyField cell16 cell8 cell32 cell40 cell56 cell24
  have same : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  rw [← same] at valid
  exact ⟨post,run,valid,otherValid,cost,remaining,locals,postCode,postDomain,endian⟩

#print axioms evaluate_htabGrow_supported_two_physical_tables
end InitECandidate.Runtime
