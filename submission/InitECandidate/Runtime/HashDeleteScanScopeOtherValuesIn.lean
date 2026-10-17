import InitECandidate.Runtime.HashDeleteScanTailFromHoleOtherValuesIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original scan local scope restores its binding after deletion returns. -/
theorem HashTableArraysInvariant.delete_scan_scope_other_values_in {F : Type}
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
    (deletedPosition : BitVec 64)
    (saved : state.memory (orderPos + hole * 8) = .word deletedPosition)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (deletedLocal : state.locals.lookup (ofString "deleted_pos") = some (.val (.word deletedPosition)))
    (otherKeyLength otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn otherTable targets state)
    (separated : ∀ address : BitVec 64,
      tablePhysicalRegion table keys stride capacity used values order orderPos address →
      ¬tablePhysicalRegion otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos address)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (budget : capacity.toNat * 55 ≤ state.clock) :
    ∃ post,
      evaluateHOLFiniteState state
        (.dec (ofString "j") .one (.var .local (ofString "i")) (.seq hashDeleteLoop hashDeleteFinalTail)) = (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post ∧
      HashTableValuesIn otherTable targets post ∧
      state.clock ≤ post.clock + capacity.toNat * 55 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨post,run,preserved,preservedValues,cost,remaining,globals,code,domain,endian⟩ := invariant.delete_scan_tail_other_values_in state
    keyLength table keys stride capacity used values order orderPos items hole bits entries reverse ordered keyValueOrder
    holeInside holeOccupied holeLocal keysLocal strideLocal sizeLocal capacityLocal usedLocal valuesLocal orderLocal reverseLocal
    linked deletedPosition saved tableLocal deletedLocal
    otherKeyLength otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherReady targets registered separated supported budget
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  have initial : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (.var .local (ofString "i")) =
      some (.val (.word hole)) := by simp [evalHOLExact,holeLocal]
  rw [initial]
  dsimp only
  have shape : shapeEqHOL .one (shapeOfHOLExact (.val (.word hole))) = true := by simp [shapeEqHOL,shapeOfHOLExact]
  rw [if_pos shape,run]
  exact ⟨_,rfl,preserved.after_read post _ otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer rfl rfl rfl rfl rfl,preservedValues.after_read rfl rfl rfl,cost,remaining,globals,code,domain,endian⟩

#print axioms HashTableArraysInvariant.delete_scan_scope_other_values_in
end InitECandidate.Runtime
