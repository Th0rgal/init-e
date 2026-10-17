import InitECandidate.Runtime.HashDeleteGuardValuesIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Capacity loading and scope restoration preserve the found deletion bound. -/
theorem HashTableArraysInvariant.delete_capacity_scope_from_hole_values_in {F : Type}
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
    (linked : HashOrderLinked used order orderPos capacity items state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn table targets state)
    (budget : capacity.toNat * 55 ≤ state.clock) :
    ∃ post,
      evaluateHOLFiniteState state (.dec (ofString "cap") .one (.load .one (hashLocalAddress (ofString "t") 16))
        (.seq hashDeleteMissingGuard hashDeleteFoundHeaderScopes)) = (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      HashTableValuesIn table targets post ∧
      state.clock ≤ post.clock + capacity.toNat * 55 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let entered := setVarHOLFinite (ofString "cap") (.val (.word capacity)) state
  have capLocal : entered.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have other : ∀ name, name ≠ ofString "cap" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have enteredInvariant := invariant.after_read state entered keyLength table keys stride capacity used values order orderPos items bits rfl rfl rfl rfl
  obtain ⟨post,run,postRegistered,cost,remaining,globals,code,domain,endian⟩ := enteredInvariant.delete_guarded_headers_from_hole_values_in entered
    keyLength table keys stride capacity used values order orderPos items hole bits
    (entries.after_read state entered used values capacity rfl rfl rfl)
    (reverse.after_read state entered used orderPos capacity items rfl rfl rfl)
    (ordered.after_memory state entered order capacity items rfl) keyValueOrder holeInside holeOccupied
    ((other _ (by decide)).trans holeLocal) capLocal
    (linked.after_read state entered used order orderPos capacity items rfl rfl rfl)
    ((other _ (by decide)).trans tableLocal) supported targets (registered.after_read rfl rfl rfl) budget
  have domains := invariant.header_domain state keyLength table keys stride capacity used values order orderPos items bits
  rw [evaluate_header_load_scope state (ofString "cap") (ofString "t") table 16 capacity _ tableLocal (domains 16 (by decide)) invariant.cell16]
  dsimp only
  rw [run]
  exact ⟨_,rfl,postRegistered.after_read rfl rfl rfl,cost,remaining,globals,code,domain,endian⟩

theorem HashTableArraysInvariant.delete_capacity_scope_missing_values_in {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos items : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
    (_linked : HashOrderLinked used order orderPos capacity items state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word capacity)))
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn table targets state) :
    ∃ post, evaluateHOLFiniteState state (.dec (ofString "cap") .one (.load .one (hashLocalAddress (ofString "t") 16))
        (.seq hashDeleteMissingGuard hashDeleteFoundHeaderScopes)) = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableValuesIn table targets post ∧
      post.clock = state.clock ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let entered := setVarHOLFinite (ofString "cap") (.val (.word capacity)) state
  have different : ofString "cap" ≠ ofString "i" := by decide
  have iLocal : entered.locals.lookup (ofString "i") = some (.val (.word capacity)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different] using indexLocal
  have capLocal : entered.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have domains := invariant.header_domain state keyLength table keys stride capacity used values order orderPos items bits
  rw [evaluate_header_load_scope state (ofString "cap") (ofString "t") table 16 capacity _ tableLocal (domains 16 (by decide)) invariant.cell16]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,evaluate_hashDelete_guard_missing entered capacity iLocal capLocal]
  exact ⟨_,rfl,registered.after_read rfl rfl rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms HashTableArraysInvariant.delete_capacity_scope_missing_values_in
#print axioms HashTableArraysInvariant.delete_capacity_scope_from_hole_values_in
end InitECandidate.Runtime
