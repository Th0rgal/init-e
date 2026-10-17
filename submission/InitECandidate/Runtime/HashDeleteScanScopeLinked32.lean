import InitECandidate.Runtime.HashDeleteScanTailFromHole32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original scan local scope restores its binding after deletion returns. -/
theorem HashTableArraysInvariant32.delete_linked_scan_scope_from_hole {F : Type}
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
    (linked : HashOrderLinked used order orderPos capacity items state)
    (deletedPosition : BitVec 64)
    (saved : state.memory (orderPos + hole * 8) = .word deletedPosition)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (deletedLocal : state.locals.lookup (ofString "deleted_pos") = some (.val (.word deletedPosition)))
    (budget : capacity.toNat * 35 ≤ state.clock) :
    ∃ post,
      evaluateHOLFiniteState state
        (.dec (ofString "j") .one (.var .local (ofString "i")) (.seq hashDeleteLoop hashDeleteFinalTail)) = (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      state.clock ≤ post.clock + capacity.toNat * 35 ∧ post.clock ≤ state.clock ∧
      HashOrderLinked used order orderPos capacity (items - 1) post := by
  obtain ⟨post,run,cost,remaining,postLinked⟩ := invariant.delete_linked_scan_tail_from_hole state
    table keys stride capacity used values order orderPos items hole bits entries reverse ordered keyValueOrder
    holeInside holeOccupied holeLocal keysLocal strideLocal sizeLocal capacityLocal usedLocal valuesLocal orderLocal reverseLocal
    linked deletedPosition saved tableLocal deletedLocal budget
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  have initial : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (.var .local (ofString "i")) =
      some (.val (.word hole)) := by simp [evalHOLExact,holeLocal]
  rw [initial]
  dsimp only
  have shape : shapeEqHOL .one (shapeOfHOLExact (.val (.word hole))) = true := by simp [shapeEqHOL,shapeOfHOLExact]
  rw [if_pos shape,run]
  exact ⟨_,rfl,cost,remaining,postLinked.after_read post _ used order orderPos capacity (items - 1) rfl rfl rfl⟩

#print axioms HashTableArraysInvariant32.delete_linked_scan_scope_from_hole
end InitECandidate.Runtime
