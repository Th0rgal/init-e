import InitECandidate.Runtime.HashGrowDisjointTable32
import InitECandidate.Runtime.HashTableKeyValueLayout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual growth returns both the relocated and protected live table states. -/
theorem evaluate_htabGrow32_two_tables {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer capacity stride keys values order items : BitVec 64) (bits : Nat)
    (tableArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [tableArgument] = some [.val (.word table)])
    (code : state.code = originalRuntimeCode) (power : capacity.toNat = 2 ^ bits)
    (old : HashGrowOldArrays table keys stride values order capacity items pointer.toNat state)
    (strideAligned : stride.toNat % 8 = 0) (fits : 32 ≤ stride.toNat) (strideBound : stride.toNat ≤ 56)
    (pointerAligned : pointer.toNat % 8 = 0) (headerBefore : table.toNat + 72 ≤ pointer.toNat)
    (pointerBound : pointer.toNat ≤ 33806089496)
    (capacityBound : capacity.toNat ≤ 33806089496)
    (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (ticks : (capacity * 2).toNat + 7 + items.toNat * ((capacity * 2).toNat + 36) ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (keyField : state.memory (table + 0) = .word (32 : BitVec 64))
    (cell16 : state.memory (table + 16) = .word capacity)
    (cell8 : state.memory (table + 8) = .word stride)
    (cell32 : state.memory (table + 32) = .word keys)
    (cell40 : state.memory (table + 40) = .word values)
    (cell56 : state.memory (table + 56) = .word order)
    (cell24 : state.memory (table + 24) = .word items)
    (otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64)
    (otherBits : Nat)
    (otherReady : HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (separate : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat ∨ table.toNat + 72 ≤ otherTable.toNat) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_grow") [tableArgument]) = (none,post) ∧
      HashTableReady32 table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride) items (bits + 1)
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post ∧
      HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post ∧
      state.clock ≤ post.clock + (capacity * 2).toNat + 7 + items.toNat * ((capacity * 2).toNat + 36) ∧
      post.clock ≤ state.clock ∧ post.locals = state.locals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨post,run,otherValid,cost,remaining,locals,postCode,addresses,endian⟩ :=
    evaluate_htabGrow32_preserves_disjoint_table state table pointer capacity stride keys values order items bits tableArgument arguments code power old
      strideAligned fits strideBound pointerAligned headerBefore pointerBound capacityBound safePlan ticks heap domain
      keyField cell16 cell8 cell32 cell40 cell56 cell24
      otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherReady separate
  obtain ⟨checked,checkedRun,valid,ordered,words,reverse,linked,_⟩ :=
    evaluate_htabGrow32_call_outside_header state table pointer capacity stride keys values order items bits tableArgument arguments code power old
      strideAligned fits strideBound pointerAligned headerBefore pointerBound capacityBound safePlan ticks heap domain
      keyField cell16 cell8 cell32 cell40 cell56 cell24
  have same : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  rw [← same] at valid ordered words reverse linked
  obtain ⟨frontierPost,frontierRun,_,_,_,_,_,_,_,_,_,_,frontier,_⟩ :=
    evaluate_htabGrow32_call_frontier state table pointer capacity stride keys values order items bits tableArgument arguments code power old
      strideAligned fits strideBound pointerAligned headerBefore pointerBound capacityBound safePlan ticks heap domain
      keyField cell16 cell8 cell32 cell40 cell56 cell24
  have sameFrontier : post = frontierPost := congrArg Prod.snd (run.symm.trans frontierRun)
  rw [← sameFrontier] at frontier
  exact ⟨post,run,⟨⟨valid,ordered,frontier⟩,words,reverse,linked,
    htabGrow_keys_before_values pointer capacity stride pointerBound capacityBound strideBound safePlan⟩,
    otherValid,cost,remaining,locals,postCode,addresses,endian⟩

#print axioms evaluate_htabGrow32_two_tables
end InitECandidate.Runtime
