import InitECandidate.Runtime.HashGrowRehashLoop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def hashGrowRehashScope : ProgHOL 64 :=
  .dec (ofString "k") .one (.const 0) (.seq hashGrowRehashLoop (.return (.const 0)))

theorem source_htabGrow_rehash_scope_exact :
    sourceFindLocalScope (ofString "k") (sourceFunctionBody Guest.guestFn_htab_grow) = some hashGrowRehashScope :=
  source_htabGrow_rehash_scope

/-- Complete original rehash suffix from its zero counter declaration through
return, preserving the old arrays and reaching the final item-count invariant. -/
theorem evaluate_hashGrow_rehash_scope {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos oldKeys oldValues oldOrder oldCapacity items : BitVec 64)
    (bits frontier : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos 0 bits state)
    (old : HashGrowOldArrays table oldKeys stride oldValues oldOrder oldCapacity items frontier state)
    (beforeKeys : frontier ≤ keys.toNat) (beforeValues : frontier ≤ values.toNat)
    (itemsFit : items.toNat < capacity.toNat)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word oldKeys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (valuesLocal : state.locals.lookup (ofString "vals") = some (.val (.word oldValues)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word oldOrder)))
    (itemsLocal : state.locals.lookup (ofString "nitems") = some (.val (.word items)))
    (budget : items.toNat * (capacity.toNat + 36) ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state hashGrowRehashScope = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableArraysInvariant32 table keys stride capacity used values order orderPos items bits post ∧
      HashGrowOldArrays table oldKeys stride oldValues oldOrder oldCapacity items frontier post ∧
      state.clock ≤ post.clock + items.toNat * (capacity.toNat + 36) ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ watched : BitVec 64, table.toNat + 72 ≤ watched.toNat → watched.toNat < frontier →
        post.memory watched = state.memory watched) := by
  let entered := setVarHOLFinite (ofString "k") (.val (.word (0 : BitVec 64))) state
  have validEntry := invariant.after_read state entered table keys stride capacity used values order orderPos 0 bits rfl rfl rfl rfl
  have oldEntry := old.preserved state entered table oldKeys stride oldValues oldOrder oldCapacity items frontier rfl
    (by intro watched lower upper; rfl)
  have other : ∀ name, name ≠ ofString "k" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have counter : entered.locals.lookup (ofString "k") = some (.val (.word (0 : BitVec 64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨post,loop,valid,oldPost,_,cost,remaining,globals,code,addresses,endian,_,frame⟩ :=
    evaluate_hashGrow_rehash_loop table keys stride capacity used values order orderPos oldKeys oldValues oldOrder oldCapacity items bits frontier
      beforeKeys beforeValues itemsFit items.toNat entered 0 validEntry oldEntry
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
  refine ⟨_,rfl,valid.after_read post _ table keys stride capacity used values order orderPos items bits rfl rfl rfl rfl,
    oldPost.preserved post _ table oldKeys stride oldValues oldOrder oldCapacity items frontier rfl
      (by intro watched lower upper; rfl),cost,remaining,globals,code,addresses,endian,frame⟩

#print axioms source_htabGrow_rehash_scope_exact
#print axioms evaluate_hashGrow_rehash_scope
end InitECandidate.Runtime
