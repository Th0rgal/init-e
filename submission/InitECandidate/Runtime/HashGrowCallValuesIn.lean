import InitECandidate.Runtime.HashGrowCallSafePlanSupported
import InitECandidate.Runtime.HashGrowBodyValuesIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual successful growth calls retain registered values through argument
binding, call entry and caller-local restoration. -/
theorem evaluate_htabGrow_call_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
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
      HashTableArraysInvariant keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
        (htabGrowOrderPos pointer capacity stride) items (bits + 1) post ∧
      HashOrderEntriesBound (htabGrowOrder pointer capacity stride) (capacity * 2) items post ∧
      HashValueEntriesWord (htabGrowUsed pointer capacity stride) (htabGrowValues pointer capacity stride) (capacity * 2) post ∧
      HashReverseEntriesBound (htabGrowUsed pointer capacity stride) (htabGrowOrderPos pointer capacity stride) (capacity * 2) items post ∧
      HashOrderLinked (htabGrowUsed pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride) (capacity * 2) items post ∧
      HashGrowOldArrays table keys stride values order capacity items pointer.toNat post ∧
      HashTableValuesIn table targets post ∧ HashOrderValuesIn order values items targets post ∧
      state.clock ≤ post.clock + (capacity * 2).toNat + 7 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ∧
      post.clock ≤ state.clock ∧ post.locals = state.locals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ watched : BitVec 64, table.toNat + 72 ≤ watched.toNat → watched.toNat < pointer.toNat →
        post.memory watched = state.memory watched) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "t",.val (.word table))
  let entry := callEntryStateHOLFinite state callee
  have tableLocal : entry.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have oldEntry := old.preserved state entry table keys stride values order capacity items pointer.toNat rfl
    (by intro watched lower upper; rfl)
  obtain ⟨post,body,valid,postEntries,postValues,postReverse,postLinked,postOld,registeredPost,oldRegisteredPost,cost,remaining,postCode,addresses,endian,frame⟩ :=
    evaluate_source_htabGrow_values_in entry keyLength table pointer capacity stride keys values order items bits supported code power oldEntry
      strideAligned fits strideBound pointerAligned headerBefore pointerBound capacityBound safePlan
      (by change (capacity * 2).toNat + 6 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ≤ state.clock - 1; omega)
      heap domain tableLocal keyField cell16 cell8 cell32 cell40 cell56 cell24 targets headerValues valuesEnd (oldRegistered.after_memory rfl)
  have installed : state.code.lookup (ofString "htab_grow") =
      some ([(ofString "t",.one)],sourceFunctionBody Guest.guestFn_htab_grow,.one) := by
    rw [code]; exact originalRuntimeCode_hashGrow_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "htab_grow") (ofString "t")
    (sourceFunctionBody Guest.guestFn_htab_grow) table installed
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "htab_grow") [tableArgument]
    [.val (.word table)] (sourceFunctionBody Guest.guestFn_htab_grow) callee .one (.val (.word 0)) post arguments lookup (by omega) body
    (by simp [shapeOfHOLExact,shapeEqHOL])
  refine ⟨{post with locals := state.locals},call,
    valid.after_read post _ keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
      (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride)
      items (bits + 1) rfl rfl rfl rfl,
    postEntries.after_memory post _ (htabGrowOrder pointer capacity stride) (capacity * 2) items rfl,
    postValues.after_read post _ (htabGrowUsed pointer capacity stride) (htabGrowValues pointer capacity stride) (capacity * 2) rfl rfl rfl,
    postReverse.after_read post _ (htabGrowUsed pointer capacity stride) (htabGrowOrderPos pointer capacity stride) (capacity * 2) items rfl rfl rfl,
    postLinked.after_read post _ (htabGrowUsed pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride) (capacity * 2) items rfl rfl rfl,
    postOld.preserved post _ table keys stride values order capacity items pointer.toNat rfl (by intro watched lower upper; rfl),
    registeredPost.after_read rfl rfl rfl,oldRegisteredPost.after_memory rfl,?_,?_,rfl,postCode,addresses,endian,frame⟩
  · change state.clock ≤ post.clock + (capacity * 2).toNat + 7 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4)
    change state.clock - 1 ≤ post.clock + (capacity * 2).toNat + 6 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) at cost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ state.clock - 1 at remaining
    omega

#print axioms evaluate_htabGrow_call_values_in
end InitECandidate.Runtime
