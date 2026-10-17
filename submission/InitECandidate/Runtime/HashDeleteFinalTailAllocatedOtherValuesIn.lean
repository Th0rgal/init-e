import InitECandidate.Runtime.HashDeleteFinalTailOtherValuesIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- One allocation separation condition frames the complete deletion suffix. -/
theorem evaluate_hashDelete_final_tail_allocated_other_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos items hole deletedPosition lastSlot cell : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
    (holeInside : hole.toNat < capacity.toNat) (lastInside : lastSlot.toNat < capacity.toNat)
    (positive : 0 < items.toNat) (deletedBound : deletedPosition.toNat < items.toNat)
    (cellMemory : state.memory (panByteAlignHOL (used + hole)) = .word cell)
    (lastCell : state.memory (order + (items - 1) * 8) = .word lastSlot)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (deletedLocal : state.locals.lookup (ofString "deleted_pos") = some (.val (.word deletedPosition)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (otherKeyLength otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (ready : HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn otherTable targets state)
    (separate : ∀ address : BitVec 64,
      tablePhysicalRegion table keys stride capacity used values order orderPos address →
      ¬tablePhysicalRegion otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos address) :
    ∃ post, evaluateHOLFiniteState state hashDeleteFinalTail = (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post ∧
      HashTableValuesIn otherTable targets post ∧
      post.clock = state.clock ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have hk := invariant.headerKeys
  have ku := invariant.keysBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  have countAddress : (table + 24).toNat = table.toNat + 24 := by
    rw [BitVec.toNat_add_of_lt (by change table.toNat + 24 < 2 ^ 64; omega)]
    rfl
  apply evaluate_hashDelete_final_tail_other_values_in state keyLength table keys stride capacity used values order orderPos items hole deletedPosition lastSlot cell bits
    invariant holeInside lastInside positive deletedBound cellMemory lastCell tableLocal orderLocal reverseLocal deletedLocal usedLocal holeLocal
    otherKeyLength otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits ready targets registered
  · intro address lower upper
    exact separate address (Or.inr (Or.inr (Or.inl ⟨lower,upper⟩)))
  · intro address lower upper
    exact separate address (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨lower,upper⟩)))))
  · intro address lower upper
    exact separate address (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨lower,upper⟩)))))
  · exact separate (table + 24) (Or.inl ⟨by omega,by omega⟩)

#print axioms evaluate_hashDelete_final_tail_allocated_other_values_in
end InitECandidate.Runtime
