import InitECandidate.Runtime.HashDeleteScanScopeValuesIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Load the deleted position from the live reverse link before scanning. -/
theorem HashTableArraysInvariant.delete_saved_scope_from_hole_values_in {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos items hole : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
    (entries : HashValueEntriesWord used values capacity state)
    (reverse : HashReverseEntriesBound used orderPos capacity items state)
    (ordered : HashOrderEntriesBound order capacity items state)
    (keyValueOrder : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (holeInside : hole.toNat < capacity.toNat)
    (holeOccupied : hashOccupancyRead state used hole ≠ some 0)
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (sizeLocal : state.locals.lookup (ofString "klen") = some (.val (.word keyLength)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (valuesLocal : state.locals.lookup (ofString "vals") = some (.val (.word values)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (linked : HashOrderLinked used order orderPos capacity items state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn table targets state)
    (budget : capacity.toNat * 55 ≤ state.clock) :
    ∃ post,
      evaluateHOLFiniteState state
        (.dec (ofString "deleted_pos") .one (.load .one (hashOrderAddress (ofString "order_pos") (ofString "i")))
          (.dec (ofString "j") .one (.var .local (ofString "i")) (.seq hashDeleteLoop hashDeleteFinalTail))) = (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      HashTableValuesIn table targets post ∧
      state.clock ≤ post.clock + capacity.toNat * 55 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨deletedPosition,_,saved,_⟩ := linked hole holeInside holeOccupied
  let entered := setVarHOLFinite (ofString "deleted_pos") (.val (.word deletedPosition)) state
  have other : ∀ name, name ≠ ofString "deleted_pos" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have deletedLocal : entered.locals.lookup (ofString "deleted_pos") = some (.val (.word deletedPosition)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have enteredInvariant := invariant.after_read state entered keyLength table keys stride capacity used values order orderPos items bits rfl rfl rfl rfl
  obtain ⟨post,run,postRegistered,cost,remaining,globals,code,domain,endian⟩ := enteredInvariant.delete_scan_scope_from_hole_values_in entered
    keyLength table keys stride capacity used values order orderPos items hole bits
    (entries.after_read state entered used values capacity rfl rfl rfl)
    (reverse.after_read state entered used orderPos capacity items rfl rfl rfl)
    (ordered.after_memory state entered order capacity items rfl) keyValueOrder holeInside holeOccupied
    ((other _ (by decide)).trans holeLocal) ((other _ (by decide)).trans keysLocal)
    ((other _ (by decide)).trans strideLocal) ((other _ (by decide)).trans sizeLocal)
    ((other _ (by decide)).trans capacityLocal) ((other _ (by decide)).trans usedLocal)
    ((other _ (by decide)).trans valuesLocal) ((other _ (by decide)).trans orderLocal)
    ((other _ (by decide)).trans reverseLocal)
    (linked.after_read state entered used order orderPos capacity items rfl rfl rfl) deletedPosition saved
    ((other _ (by decide)).trans tableLocal) deletedLocal supported targets (registered.after_read rfl rfl rfl) budget
  have facts := invariant.insertion_memory state keyLength table keys stride capacity used values order orderPos items bits
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (hashOrderAddress (ofString "order_pos") (ofString "i"))) = some (.val (.word deletedPosition)) := by
    simp only [evalHOLExact,isWfShapeExactHOL]
    rw [eval_hashOrderAddress state _ _ orderPos hole reverseLocal holeLocal]
    simp [memLoadHOLExact]
    exact ⟨facts.orderPosDomain hole holeInside,saved⟩
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [loaded]
  dsimp only
  have shape : shapeEqHOL .one (shapeOfHOLExact (.val (.word deletedPosition))) = true := by simp [shapeEqHOL,shapeOfHOLExact]
  rw [if_pos shape,run]
  exact ⟨_,rfl,postRegistered.after_read rfl rfl rfl,cost,remaining,globals,code,domain,endian⟩

#print axioms HashTableArraysInvariant.delete_saved_scope_from_hole_values_in
end InitECandidate.Runtime
