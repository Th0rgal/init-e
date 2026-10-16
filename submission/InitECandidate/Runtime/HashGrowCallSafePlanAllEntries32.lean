import InitECandidate.Runtime.HashGrowBodySafePlanAllEntries32
import InitECandidate.Runtime.OriginalHashGrowCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual original successful growth call, including binding, call-entry
clock and caller-local restoration, with complete ranked rehash execution. -/
theorem evaluate_htabGrow32_call_safe_plan_all_entries {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (cell24 : state.memory (table + 24) = .word items) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_grow") [tableArgument]) = (none,post) ∧
      HashTableArraysInvariant32 table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
        (htabGrowOrderPos pointer capacity stride) items (bits + 1) post ∧
      HashOrderEntriesBound (htabGrowOrder pointer capacity stride) (capacity * 2) items post ∧
      HashValueEntriesWord (htabGrowUsed pointer capacity stride) (htabGrowValues pointer capacity stride) (capacity * 2) post ∧
      HashReverseEntriesBound (htabGrowUsed pointer capacity stride) (htabGrowOrderPos pointer capacity stride) (capacity * 2) items post ∧
      HashGrowOldArrays table keys stride values order capacity items pointer.toNat post ∧
      state.clock ≤ post.clock + (capacity * 2).toNat + 7 + items.toNat * ((capacity * 2).toNat + 36) ∧
      post.clock ≤ state.clock ∧ post.locals = state.locals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ watched : BitVec 64, table.toNat + 72 ≤ watched.toNat → watched.toNat < pointer.toNat →
        post.memory watched = state.memory watched) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "t",.val (.word table))
  let entry := callEntryStateHOLFinite state callee
  have tableLocal : entry.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have oldEntry := old.preserved state entry table keys stride values order capacity items pointer.toNat rfl
    (by intro watched lower upper; rfl)
  obtain ⟨post,body,valid,postEntries,postValues,postReverse,postOld,cost,remaining,postCode,addresses,endian,frame⟩ :=
    evaluate_source_htabGrow32_safe_plan_all_entries entry table pointer capacity stride keys values order items bits code power oldEntry
      strideAligned fits strideBound pointerAligned headerBefore pointerBound capacityBound safePlan
      (by change (capacity * 2).toNat + 6 + items.toNat * ((capacity * 2).toNat + 36) ≤ state.clock - 1; omega)
      heap domain tableLocal keyField cell16 cell8 cell32 cell40 cell56 cell24
  have installed : state.code.lookup (ofString "htab_grow") =
      some ([(ofString "t",.one)],sourceFunctionBody Guest.guestFn_htab_grow,.one) := by
    rw [code]; exact originalRuntimeCode_hashGrow_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "htab_grow") (ofString "t")
    (sourceFunctionBody Guest.guestFn_htab_grow) table installed
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "htab_grow") [tableArgument]
    [.val (.word table)] (sourceFunctionBody Guest.guestFn_htab_grow) callee .one (.val (.word 0)) post arguments lookup (by omega) body
    (by simp [shapeOfHOLExact,shapeEqHOL])
  refine ⟨{post with locals := state.locals},call,
    valid.after_read post _ table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
      (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride)
      items (bits + 1) rfl rfl rfl rfl,
    postEntries.after_memory post _ (htabGrowOrder pointer capacity stride) (capacity * 2) items rfl,
    postValues.after_read post _ (htabGrowUsed pointer capacity stride) (htabGrowValues pointer capacity stride) (capacity * 2) rfl rfl rfl,
    postReverse.after_read post _ (htabGrowUsed pointer capacity stride) (htabGrowOrderPos pointer capacity stride) (capacity * 2) items rfl rfl rfl,
    postOld.preserved post _ table keys stride values order capacity items pointer.toNat rfl (by intro watched lower upper; rfl),
    ?_,?_,rfl,postCode,addresses,endian,frame⟩
  · change state.clock ≤ post.clock + (capacity * 2).toNat + 7 + items.toNat * ((capacity * 2).toNat + 36)
    change state.clock - 1 ≤ post.clock + (capacity * 2).toNat + 6 + items.toNat * ((capacity * 2).toNat + 36) at cost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ state.clock - 1 at remaining
    omega

#print axioms evaluate_htabGrow32_call_safe_plan_all_entries
end InitECandidate.Runtime
