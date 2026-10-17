import InitECandidate.Runtime.HashGrowReadySupported
import InitECandidate.Runtime.HashGrowCallValuesIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- One actual growth output establishes the complete ready-table invariant
and preserves registered-pointer membership, including old rehash sources. -/
theorem evaluate_htabGrow_ready_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (targets : Set (BitVec 64)) (headerValues : table.toNat + 72 ≤ values.toNat)
    (valuesEnd : values.toNat + capacity.toNat * 8 ≤ pointer.toNat)
    (oldRegistered : HashOrderValuesIn order values items targets state) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_grow") [tableArgument]) = (none,post) ∧
      HashTableReady keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
        (htabGrowOrderPos pointer capacity stride) items (bits + 1)
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post ∧
      HashGrowOldArrays table keys stride values order capacity items pointer.toNat post ∧
      HashTableValuesIn table targets post ∧ HashOrderValuesIn order values items targets post ∧
      state.clock ≤ post.clock + (capacity * 2).toNat + 7 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ∧
      post.clock ≤ state.clock ∧ post.locals = state.locals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ watched : BitVec 64, table.toNat + 72 ≤ watched.toNat → watched.toNat < pointer.toNat →
        post.memory watched = state.memory watched) := by
  obtain ⟨post,run,arrays,entries,words,reverse,linked,oldPost,registeredPost,oldRegisteredPost,cost,remaining,locals,postCode,addresses,endian,frame⟩ :=
    evaluate_htabGrow_call_values_in state keyLength table pointer capacity stride keys values order items bits supported tableArgument arguments code power old
      strideAligned fits strideBound pointerAligned headerBefore pointerBound capacityBound safePlan ticks heap domain
      keyField cell16 cell8 cell32 cell40 cell56 cell24 targets headerValues valuesEnd oldRegistered
  obtain ⟨checked,checkedRun,_,_,_,_,_,_,_,_,_,_,frontier,_⟩ :=
    evaluate_htabGrow_supported_call_frontier state keyLength table pointer capacity stride keys values order items bits supported tableArgument arguments code power old
      strideAligned fits strideBound pointerAligned headerBefore pointerBound capacityBound safePlan ticks heap domain
      keyField cell16 cell8 cell32 cell40 cell56 cell24
  have same : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  rw [← same] at frontier
  exact ⟨post,run,⟨⟨arrays,entries,frontier⟩,words,reverse,linked,
    htabGrow_keys_before_values pointer capacity stride pointerBound capacityBound strideBound safePlan⟩,
    oldPost,registeredPost,oldRegisteredPost,cost,remaining,locals,postCode,addresses,endian,frame⟩

#print axioms evaluate_htabGrow_ready_values_in
end InitECandidate.Runtime
