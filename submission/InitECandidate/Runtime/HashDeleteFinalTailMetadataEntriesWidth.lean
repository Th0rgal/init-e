import InitECandidate.Runtime.HashDeleteFinalTailMetadataWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Forward order bounds supply the final slot witness and its range. -/
theorem evaluate_hashDelete_final_tail_metadata_entries_width {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos items hole deletedPosition : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
    (holeInside : hole.toNat < capacity.toNat)
    (deletedBound : deletedPosition.toNat < items.toNat)
    (ordered : HashOrderEntriesBound order capacity items state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (deletedLocal : state.locals.lookup (ofString "deleted_pos") = some (.val (.word deletedPosition)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole))) :
    ∃ post, evaluateHOLFiniteState state hashDeleteFinalTail = (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      post.clock = state.clock ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have positive : 0 < items.toNat := by omega
  have subtraction : (items - (1 : BitVec 64)).toNat = items.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1 ≤ items.toNat; omega))]
    rfl
  obtain ⟨lastSlot,lastCell,lastInside⟩ := ordered (items - 1) (by omega)
  obtain ⟨cell,cellMemory⟩ : ∃ cell, state.memory (panByteAlignHOL (used + hole)) = HolWordLab.word cell := by
    cases memory : state.memory (panByteAlignHOL (used + hole)) with
    | word cell => exact ⟨cell,rfl⟩
  exact evaluate_hashDelete_final_tail_metadata_width state keyLength table keys stride capacity used values order orderPos items hole deletedPosition lastSlot cell bits
    invariant holeInside lastInside positive deletedBound cellMemory lastCell tableLocal orderLocal reverseLocal deletedLocal usedLocal holeLocal

#print axioms evaluate_hashDelete_final_tail_metadata_entries_width
end InitECandidate.Runtime
