import InitECandidate.Runtime.HashGrowRehashStepSupported
import InitECandidate.Runtime.HashGrowRehashInsertValuesIn
import InitECandidate.Runtime.HashOrderValuesIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original rehash body selects a live old order entry, reinserts its
registered pointer, advances the counter and restores its temporary slot local. -/
theorem evaluate_hashGrow_rehash_body_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (targets : Set (BitVec 64)) (newEntries : HashTableValuesIn table targets state)
    (oldEntries : HashOrderValuesIn oldOrder oldValues items targets state) :
    HashTableValuesIn table targets (evaluateHOLFiniteState state hashGrowRehashBody).2 := by
  obtain ⟨slot,slotMemory,slotInside⟩ := old.entries count inside
  obtain ⟨aligned,words,bytes,valueCell⟩ := hashGrow_old_slot_domains_width state keyLength oldKeys stride oldValues oldCapacity slot slotInside
    old.keysAligned invariant.strideAligned old.valuesAligned invariant.fits old.keyBound old.valueBound old.keyDomain old.valueDomain
  have counterInside : count.toNat < oldCapacity.toNat := by have bound := old.itemsBound; omega
  have interval := hashFind_slot_offset oldOrder count 8 oldCapacity 8 0 counterInside
    (by change oldOrder.toNat + oldCapacity.toNat * 8 ≤ 33806089496; exact old.orderBound)
    old.orderAligned (by decide) (by decide) (by decide)
  have orderDomain : state.memaddrs (oldOrder + count * 8) := old.orderDomain _ (by simpa using interval.2.1) (by simpa using interval.2.2)
  let entered := setVarHOLFinite (ofString "i") (.val (.word slot)) state
  have validEntry := invariant.after_read state entered keyLength table keys stride capacity used values order orderPos count bits rfl rfl rfl rfl
  have other : ∀ name, name ≠ ofString "i" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have slotLocal : entered.locals.lookup (ofString "i") = some (.val (.word slot)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨post,tail,_,preserved,_,_,_,_,_,_,_,_⟩ :=
    evaluate_hashGrow_rehash_insert_values_in entered keyLength table keys stride capacity used values order orderPos count oldKeys oldValues slot bits frontier
      supported validEntry beforeKeys beforeValues ((other _ (by decide)).trans tableLocal) ((other _ (by decide)).trans keysLocal)
      ((other _ (by decide)).trans strideLocal) ((other _ (by decide)).trans valuesLocal) slotLocal ((other _ (by decide)).trans countLocal)
      valueCell aligned words bytes (by omega) budget keysBeforeValues targets (newEntries.after_read rfl rfl rfl)
      (oldEntries count inside slot slotMemory)
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (hashOrderAddress (ofString "order") (ofString "k"))) = some (.val (.word slot)) := by
    simp only [evalHOLExact,isWfShapeExactHOL]
    rw [eval_hashOrderAddress state (ofString "order") (ofString "k") oldOrder count orderLocal countLocal]
    simp [memLoadHOLExact]
    exact ⟨orderDomain,slotMemory⟩
  rw [source_hashGrow_rehash_body,evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [loaded]
  dsimp only
  have shapeOk : shapeEqHOL .one (shapeOfHOLExact (.val (.word slot))) = true := by simp [shapeEqHOL,shapeOfHOLExact]
  rw [if_pos shapeOk]
  dsimp only [hashGrowRehashInsertAdvance,entered] at tail
  rw [tail]
  exact preserved.after_read rfl rfl rfl

#print axioms evaluate_hashGrow_rehash_body_values_in
end InitECandidate.Runtime
