import InitECandidate.Runtime.HashDeleteGuardOther32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Capacity loading and scope restoration preserve the found deletion bound. -/
theorem HashTableArraysInvariant32.delete_capacity_scope_with_other_from_hole {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos items hole : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos items bits state)
    (entries : HashValueEntriesWord used values capacity state)
    (reverse : HashReverseEntriesBound used orderPos capacity items state)
    (ordered : HashOrderEntriesBound order capacity items state)
    (keyValueOrder : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (holeInside : hole.toNat < capacity.toNat)
    (holeOccupied : hashOccupancyRead state used hole ≠ some 0)
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (linked : HashOrderLinked used order orderPos capacity items state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (separated : orderPos.toNat + capacity.toNat * 8 ≤ otherTable.toNat ∨
      otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat)
    (budget : capacity.toNat * 35 ≤ state.clock) :
    ∃ post,
      evaluateHOLFiniteState state (.dec (ofString "cap") .one (.load .one (hashLocalAddress (ofString "t") 16))
        (.seq hashDeleteMissingGuard hashDeleteFoundHeaderScopes)) = (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post ∧
      state.clock ≤ post.clock + capacity.toNat * 35 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let entered := setVarHOLFinite (ofString "cap") (.val (.word capacity)) state
  have capLocal : entered.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have other : ∀ name, name ≠ ofString "cap" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have enteredInvariant := invariant.after_read state entered table keys stride capacity used values order orderPos items bits rfl rfl rfl rfl
  have enteredOther := otherReady.after_read state entered otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer rfl rfl rfl rfl rfl
  obtain ⟨post,run,preserved,cost,remaining,globals,code,domain,endian⟩ := enteredInvariant.delete_guarded_headers_with_other_from_hole entered
    table keys stride capacity used values order orderPos items hole bits
    (entries.after_read state entered used values capacity rfl rfl rfl)
    (reverse.after_read state entered used orderPos capacity items rfl rfl rfl)
    (ordered.after_memory state entered order capacity items rfl) keyValueOrder holeInside holeOccupied
    ((other _ (by decide)).trans holeLocal) capLocal
    (linked.after_read state entered used order orderPos capacity items rfl rfl rfl)
    ((other _ (by decide)).trans tableLocal)
    otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits enteredOther separated budget
  have domains := invariant.header_domain state table keys stride capacity used values order orderPos items bits
  rw [evaluate_header_load_scope state (ofString "cap") (ofString "t") table 16 capacity _ tableLocal (domains 16 (by decide)) invariant.cell16]
  dsimp only
  rw [run]
  exact ⟨_,rfl,preserved.after_read post _ otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer rfl rfl rfl rfl rfl,cost,remaining,globals,code,domain,endian⟩

#print axioms HashTableArraysInvariant32.delete_capacity_scope_with_other_from_hole
end InitECandidate.Runtime
