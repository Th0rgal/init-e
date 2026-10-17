import InitECandidate.Runtime.HashGrowRehashScopeSupported
import InitECandidate.Runtime.HashGrowRehashLoopValuesIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual rehash scope initializes the empty new table's pointer predicate,
then retains old and new registered values through the loop and scope exit. -/
theorem evaluate_hashGrow_rehash_scope_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos oldKeys oldValues oldOrder oldCapacity items : BitVec 64)
    (bits frontier : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos 0 bits state)
    (old : HashGrowOldArrays table oldKeys stride oldValues oldOrder oldCapacity items frontier state)
    (beforeKeys : frontier ≤ keys.toNat) (beforeValues : frontier ≤ values.toNat)
    (itemsFit : items.toNat < capacity.toNat)
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word oldKeys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (valuesLocal : state.locals.lookup (ofString "vals") = some (.val (.word oldValues)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word oldOrder)))
    (itemsLocal : state.locals.lookup (ofString "nitems") = some (.val (.word items)))
    (budget : items.toNat * (capacity.toNat + keyLength.toNat + 4) ≤ state.clock)
    (targets : Set (BitVec 64)) (oldHeaderValues : table.toNat + 72 ≤ oldValues.toNat)
    (oldValuesEnd : oldValues.toNat + oldCapacity.toNat * 8 ≤ frontier)
    (oldRegistered : HashOrderValuesIn oldOrder oldValues items targets state) :
    ∃ post, evaluateHOLFiniteState state hashGrowRehashScope = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits post ∧
      HashOrderEntriesBound order capacity items post ∧
      HashValueEntriesWord used values capacity post ∧
      HashReverseEntriesBound used orderPos capacity items post ∧
      HashOrderLinked used order orderPos capacity items post ∧
      HashGrowOldArrays table oldKeys stride oldValues oldOrder oldCapacity items frontier post ∧
      HashTableValuesIn table targets post ∧ HashOrderValuesIn oldOrder oldValues items targets post ∧
      state.clock ≤ post.clock + items.toNat * (capacity.toNat + keyLength.toNat + 4) ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ watched : BitVec 64, table.toNat + 72 ≤ watched.toNat → watched.toNat < frontier →
        post.memory watched = state.memory watched) := by
  let entered := setVarHOLFinite (ofString "k") (.val (.word (0 : BitVec 64))) state
  have validEntry := invariant.after_read state entered keyLength table keys stride capacity used values order orderPos 0 bits rfl rfl rfl rfl
  have oldEntry := old.preserved state entered table oldKeys stride oldValues oldOrder oldCapacity items frontier rfl
    (by intro watched lower upper; rfl)
  have other : ∀ name, name ≠ ofString "k" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have counter : entered.locals.lookup (ofString "k") = some (.val (.word (0 : BitVec 64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨emptyValues,emptyReverse⟩ := hashEmpty_entry_invariants entered used values orderPos capacity (by
    have agreement := validEntry.agreement
    change 0 = hashOccupiedCount capacity (hashOccupancyRead entered used) at agreement
    exact agreement.symm)
  obtain ⟨post,loop,valid,entriesPost,valuesPost,reversePost,linkedPost,oldPost,registeredPost,oldRegisteredPost,_,cost,remaining,globals,code,addresses,endian,_,frame⟩ :=
    evaluate_hashGrow_rehash_loop_values_in keyLength table keys stride capacity used values order orderPos oldKeys oldValues oldOrder oldCapacity items bits frontier supported
      beforeKeys beforeValues itemsFit keysBeforeValues targets oldHeaderValues oldValuesEnd items.toNat entered 0 validEntry oldEntry (HashOrderEntriesBound.empty order capacity entered) emptyValues emptyReverse
      (HashOrderLinked.empty entered used order orderPos capacity (by
        have agreement := validEntry.agreement
        change 0 = hashOccupiedCount capacity (hashOccupancyRead entered used) at agreement
        exact agreement.symm))
      (HashTableValuesIn.empty entered table capacity used targets validEntry.cell16 validEntry.cell48 (by simpa using validEntry.agreement.symm))
      (oldRegistered.after_memory rfl)
      ((other _ (by decide)).trans tableLocal) ((other _ (by decide)).trans keysLocal)
      ((other _ (by decide)).trans strideLocal) ((other _ (by decide)).trans valuesLocal)
      ((other _ (by decide)).trans orderLocal) counter ((other _ (by decide)).trans itemsLocal)
      (by simp) (by simp) budget
  have returned : evaluateHOLFiniteState post (.return (.const 0)) =
      (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite post) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  have body := evaluate_seq_none loop returned
  unfold hashGrowRehashScope
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only [evalHOLExact]
  have shapeOk : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) = true := by simp [shapeEqHOL,shapeOfHOLExact]
  rw [if_pos shapeOk,body]
  refine ⟨_,rfl,valid.after_read post _ keyLength table keys stride capacity used values order orderPos items bits rfl rfl rfl rfl,
    entriesPost.after_memory post _ order capacity items rfl,
    valuesPost.after_read post _ used values capacity rfl rfl rfl,
    reversePost.after_read post _ used orderPos capacity items rfl rfl rfl,
    linkedPost.after_read post _ used order orderPos capacity items rfl rfl rfl,
    oldPost.preserved post _ table oldKeys stride oldValues oldOrder oldCapacity items frontier rfl
      (by intro watched lower upper; rfl),registeredPost.after_read rfl rfl rfl,oldRegisteredPost.after_memory rfl,cost,remaining,globals,code,addresses,endian,frame⟩

#print axioms evaluate_hashGrow_rehash_scope_values_in
end InitECandidate.Runtime
