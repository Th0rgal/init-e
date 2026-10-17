import InitECandidate.Runtime.HashGrowOldArrays
import InitECandidate.Runtime.HashGrowRehashBodyArraysSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- One actual original rehash iteration preserves the complete pair of old
and new table invariants, selecting its old slot from the order memory. -/
theorem evaluate_hashGrow_rehash_step_supported {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count oldKeys oldValues oldOrder oldCapacity items : BitVec 64)
    (bits frontier : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (old : HashGrowOldArrays table oldKeys stride oldValues oldOrder oldCapacity items frontier state)
    (beforeKeys : frontier ≤ keys.toNat) (beforeValues : frontier ≤ values.toNat)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word oldKeys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (valuesLocal : state.locals.lookup (ofString "vals") = some (.val (.word oldValues)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word oldOrder)))
    (countLocal : state.locals.lookup (ofString "k") = some (.val (.word count)))
    (inside : count.toNat < items.toNat) (itemsFit : items.toNat < capacity.toNat)
    (budget : capacity.toNat + keyLength.toNat + 3 ≤ state.clock)
    (entries : HashOrderEntriesBound order capacity count state)
    (valueEntries : HashValueEntriesWord used values capacity state)
    (reverseEntries : HashReverseEntriesBound used orderPos capacity count state)
    (linked : HashOrderLinked used order orderPos capacity count state)
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat) :
    ∃ post, evaluateHOLFiniteState state hashGrowRehashBody = (none,post) ∧
      HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos (count + 1) bits post ∧
      HashOrderEntriesBound order capacity (count + 1) post ∧
      HashValueEntriesWord used values capacity post ∧
      HashReverseEntriesBound used orderPos capacity (count + 1) post ∧
      HashOrderLinked used order orderPos capacity (count + 1) post ∧
      HashGrowOldArrays table oldKeys stride oldValues oldOrder oldCapacity items frontier post ∧
      state.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 3 ∧ post.clock ≤ state.clock ∧
      post.locals = (setVarHOLFinite (ofString "k") (.val (.word (count + 1))) state).locals ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      ∀ watched : BitVec 64, table.toNat + 72 ≤ watched.toNat → watched.toNat < frontier →
        post.memory watched = state.memory watched := by
  obtain ⟨slot,memory,slotInside⟩ := old.entries count inside
  obtain ⟨post,run,valid,entriesAfter,words,reverse,linkedAfter,cost,remaining,locals,globals,code,addresses,endian,frame⟩ :=
    evaluate_hashGrow_rehash_body_from_arrays_supported state keyLength table keys stride capacity used values order orderPos count
      oldKeys oldValues oldOrder oldCapacity slot bits frontier supported invariant beforeKeys beforeValues
      tableLocal keysLocal strideLocal valuesLocal orderLocal memory countLocal slotInside (by have := old.itemsBound; omega)
      old.keysAligned old.valuesAligned old.orderAligned old.keyBound old.valueBound old.orderBound old.keyDomain old.valueDomain old.orderDomain
      (by omega) budget entries valueEntries reverseEntries linked keysBeforeValues
  exact ⟨post,run,valid,entriesAfter,words,reverse,linkedAfter,old.preserved state post table oldKeys stride oldValues oldOrder oldCapacity items frontier addresses frame,
    cost,remaining,locals,globals,code,addresses,endian,frame⟩

#print axioms evaluate_hashGrow_rehash_step_supported
end InitECandidate.Runtime
