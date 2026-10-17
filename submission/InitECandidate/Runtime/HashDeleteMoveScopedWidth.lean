import InitECandidate.Runtime.HashDeleteMoveAllocatedWidth
import InitECandidate.Runtime.HashDeleteMoveScopeRun
import InitECandidate.Runtime.LocalScopeRestore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashDelete_move_scoped_width {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength keys stride hole scan values order orderPos used capacity items : BitVec 64)
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (scanLocal : state.locals.lookup (ofString "j") = some (.val (.word scan)))
    (sizeLocal : state.locals.lookup (ofString "klen") = some (.val (.word keyLength)))
    (hash : BitVec 64)
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (moves : hashDeleteMoveRequired hole scan (hash &&& (capacity - 1)))
    (table : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
    (scanInside : scan.toNat < capacity.toNat)
    (occupied : hashOccupancyRead state used scan ≠ some 0)
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (budget : keyLength.toNat + 1 ≤ state.clock)
    (valuesLocal : state.locals.lookup (ofString "vals") = some (.val (.word values)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (entries : HashReverseEntriesBound used orderPos capacity items state)
    (orderEntries : HashOrderEntriesBound order capacity items state)
    (holeInside : hole.toNat < capacity.toNat)
    (valueEntries : HashValueEntriesWord used values capacity state)
 :
    ∃ post, evaluateHOLFiniteState state hashDeleteAfterHash = (none,post) ∧
      state.clock ≤ post.clock + keyLength.toNat + 1 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ HashReverseEntriesBound used orderPos capacity items post ∧ HashOrderEntriesBound order capacity items post ∧
      (∀ slot : BitVec 64, slot.toNat < capacity.toNat →
        hashOccupancyRead post used slot = hashOccupancyRead state used slot) ∧
      post.locals.lookup (ofString "i") = some (.val (.word scan)) ∧ HashValueEntriesWord used values capacity post ∧ post.locals.lookup (ofString "j") = some (.val (.word scan)) ∧ HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits post ∧
      (∀ name, name ≠ ofString "i" → name ≠ ofString "home" → name ≠ ofString "movable" →
        post.locals.lookup name = state.locals.lookup name) := by
  let entered := hashDeleteMoveEntry state hash capacity
  have other : ∀ name, name ≠ ofString "home" → name ≠ ofString "movable" → entered.locals.lookup name = state.locals.lookup name := by
    intro name notHome notMovable
    simp [entered,hashDeleteMoveEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notHome,Ne.symm notMovable]
  have enteredInvariant := invariant.after_read state entered keyLength table keys stride capacity used values order orderPos items bits rfl rfl rfl rfl
  obtain ⟨post,run,cost,remaining,globals,code,domain,endian,reverse,ordered,occupancy,locals,words,arrays⟩ :=
    evaluate_hashDelete_move_allocated_width entered keyLength keys stride hole scan values order orderPos used capacity items
      ((other _ (by decide) (by decide)).trans keysLocal) ((other _ (by decide) (by decide)).trans strideLocal)
      ((other _ (by decide) (by decide)).trans holeLocal) ((other _ (by decide) (by decide)).trans scanLocal)
      ((other _ (by decide) (by decide)).trans sizeLocal) table bits enteredInvariant scanInside occupied keysBeforeValues budget
      ((other _ (by decide) (by decide)).trans valuesLocal) ((other _ (by decide) (by decide)).trans orderLocal)
      ((other _ (by decide) (by decide)).trans reverseLocal)
      (entries.after_read state entered used orderPos capacity items rfl rfl rfl)
      (orderEntries.after_memory state entered order capacity items rfl) holeInside
      (valueEntries.after_read state entered used values capacity rfl rfl rfl)
  have scopeRun := evaluate_hashDelete_move_scope_run state post hole scan hash capacity holeLocal scanLocal hashLocal capacityLocal moves run
  refine ⟨hashDeleteMoveExit state post,scopeRun,cost,remaining,globals,code,domain,endian,
    reverse.after_read post _ used orderPos capacity items rfl rfl rfl,
    ordered.after_memory post _ order capacity items rfl,occupancy,?_,words.after_read post _ used values capacity rfl rfl rfl,?_,arrays.after_read post _ keyLength table keys stride capacity used values order orderPos items bits rfl rfl rfl rfl,?_⟩
  · unfold hashDeleteMoveExit
    rw [restore_other_local _ _ (ofString "i") _ (by decide),restore_other_local _ _ (ofString "i") _ (by decide)]
    rw [locals]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · unfold hashDeleteMoveExit
    rw [restore_other_local _ _ (ofString "j") _ (by decide),restore_other_local _ _ (ofString "j") _ (by decide)]
    rw [locals]
    have different : ofString "i" ≠ ofString "j" := by decide
    simp only [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,if_neg different]
    exact (other _ (by decide) (by decide)).trans scanLocal
  · intro name notIndex notHome notMovable
    unfold hashDeleteMoveExit
    rw [restore_other_local _ _ name _ notHome,restore_other_local _ _ name _ notMovable,locals]
    change (entered.locals.update (ofString "i",.val (.word scan))).lookup name = _
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notIndex] using other name notHome notMovable

#print axioms evaluate_hashDelete_move_scoped_width
end InitECandidate.Runtime
