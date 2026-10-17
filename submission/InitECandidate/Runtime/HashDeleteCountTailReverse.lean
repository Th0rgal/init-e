import InitECandidate.Runtime.HashDeleteCountTail
import InitECandidate.Runtime.HashDeleteFinalReverseStores
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashDelete_count_tail_reverse {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table order orderPos deletedPosition count lastSlot used capacity hole : BitVec 64)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (deletedLocal : state.locals.lookup (ofString "deleted_pos") = some (.val (.word deletedPosition)))
    (countDomain : state.memaddrs (table + 24))
    (countCell : state.memory (table + 24) = .word count)
    (loadDomain : state.memaddrs (order + (count - 1) * 8))
    (loadCell : state.memory (order + (count - 1) * 8) = .word lastSlot)
    (orderDomain : state.memaddrs (order + deletedPosition * 8))
    (reverseDomain : state.memaddrs (orderPos + lastSlot * 8))
    (linked : HashDeleteOrderLinked used order orderPos capacity count hole deletedPosition state)
    (positive : 0 < count.toNat) (deletedBound : deletedPosition.toNat < count.toNat)
    (holeEmpty : hashOccupancyRead state used hole = some 0)
    (occupancySeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ order + deletedPosition * 8 ∧
      panByteAlignHOL (used + slot) ≠ orderPos + lastSlot * 8 ∧ panByteAlignHOL (used + slot) ≠ table + 24)
    (reverseSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      orderPos + slot * 8 ≠ table + 24 ∧ (slot ≠ lastSlot →
        orderPos + slot * 8 ≠ order + deletedPosition * 8 ∧ orderPos + slot * 8 ≠ orderPos + lastSlot * 8))
    (headerSeparate : orderPos + lastSlot * 8 ≠ table + 24) :
    ∃ post, evaluateHOLFiniteState state hashDeleteCountTail = (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      post.clock = state.clock ∧ HashReverseEntriesBound used orderPos capacity (count - 1) post := by
  classical
  obtain ⟨post,run,ticks,_,_,domain,endian,memory,_⟩ := evaluate_hashDelete_count_tail state
    table order orderPos deletedPosition count lastSlot tableLocal orderLocal reverseLocal deletedLocal
    countDomain countCell loadDomain loadCell orderDomain reverseDomain
  let written := sourceWriteWord
    (if deletedPosition = count - 1 then state else
      sourceWriteWord (sourceWriteWord state (order + deletedPosition * 8) lastSlot)
        (orderPos + lastSlot * 8) deletedPosition) (table + 24) (count - 1)
  have bound : HashReverseEntriesBound used orderPos capacity (count - 1) written := by
    by_cases same : deletedPosition = count - 1
    · simp only [written,if_pos same]
      exact (same ▸ linked).final_last_store state used order orderPos capacity count hole table positive holeEmpty
        (fun slot inside => (occupancySeparate slot inside).2.2)
        (fun slot inside => (reverseSeparate slot inside).1)
    · have subtraction : (count - (1 : BitVec 64)).toNat = count.toNat - 1 := by
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1 ≤ count.toNat; omega))]
        rfl
      have differentNat : deletedPosition.toNat ≠ (count - 1).toNat := fun equal => same (BitVec.eq_of_toNat_eq equal)
      simp only [written,if_neg same]
      exact linked.final_swap_stores state used order orderPos capacity count hole deletedPosition lastSlot table
        positive (by omega) holeEmpty loadCell occupancySeparate
        (fun slot inside different => ⟨((reverseSeparate slot inside).2 different).1,
          ((reverseSeparate slot inside).2 different).2,(reverseSeparate slot inside).1⟩) headerSeparate
  exact ⟨post,run,ticks,bound.after_read written post used orderPos capacity (count - 1) memory (by dsimp [written]; split <;> exact domain) (by dsimp [written]; split <;> exact endian)⟩

#print axioms evaluate_hashDelete_count_tail_reverse
end InitECandidate.Runtime
