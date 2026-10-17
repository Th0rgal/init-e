import InitECandidate.Runtime.HashDeleteLoopStep32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The count invariant supplies the stable empty witness; the source scan
starts at the deletion hole before its first increment. -/
theorem HashTableArraysInvariant32.delete_scan_from_hole {F : Type}
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
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (sizeLocal : state.locals.lookup (ofString "klen") = some (.val (.word (32 : BitVec 64))))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (valuesLocal : state.locals.lookup (ofString "vals") = some (.val (.word values)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (budget : capacity.toNat * 35 ≤ state.clock) :
    ∃ empty : BitVec 64, ∃ post,
      evaluateHOLFiniteState (setVarHOLFinite (ofString "j") (.val (.word hole)) state) hashDeleteLoop = (none,post) ∧
      HashDeleteLoopInvariant32 table keys stride capacity used values order orderPos items empty bits post ∧
      state.clock ≤ post.clock + capacity.toNat * 35 ∧ post.clock ≤ state.clock := by
  obtain ⟨empty,emptyInside,emptyRead⟩ := hashOccupiedCount_exists_empty capacity (hashOccupancyRead state used)
    (by rw [← invariant.agreement]; exact invariant.room)
  let entered := setVarHOLFinite (ofString "j") (.val (.word hole)) state
  have other : ∀ name, name ≠ ofString "j" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have j : entered.locals.lookup (ofString "j") = some (.val (.word hole)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have ready : HashDeleteLoopInvariant32 table keys stride capacity used values order orderPos items empty bits entered := {
    arrays := invariant.after_read state entered table keys stride capacity used values order orderPos items bits rfl rfl rfl rfl
    valuesWord := entries.after_read state entered used values capacity rfl rfl rfl
    reverse := reverse.after_read state entered used orderPos capacity items rfl rfl rfl
    ordered := ordered.after_memory state entered order capacity items rfl
    keyValueOrder := keyValueOrder
    emptyInside := emptyInside
    emptyRead := emptyRead
    keysLocal := ((other _ (by decide))).trans keysLocal
    strideLocal := ((other _ (by decide))).trans strideLocal
    sizeLocal := ((other _ (by decide))).trans sizeLocal
    capacityLocal := ((other _ (by decide))).trans capacityLocal
    usedLocal := ((other _ (by decide))).trans usedLocal
    valuesLocal := ((other _ (by decide))).trans valuesLocal
    orderLocal := ((other _ (by decide))).trans orderLocal
    reverseLocal := ((other _ (by decide))).trans reverseLocal
    indices := ⟨hole,hole,holeInside,holeInside,((other _ (by decide))).trans holeLocal,j,holeOccupied⟩
  }
  obtain ⟨post,run,valid,cost,remaining⟩ := evaluate_hashDelete_loop_capacity32 table keys stride capacity used values order orderPos items empty bits entered ready budget
  exact ⟨empty,post,run,valid,cost,remaining⟩

#print axioms HashTableArraysInvariant32.delete_scan_from_hole
end InitECandidate.Runtime
