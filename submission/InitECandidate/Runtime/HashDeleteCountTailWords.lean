import InitECandidate.Runtime.HashDeleteCountTail
import InitECandidate.Runtime.HashDeleteFinalValueWords
import InitECandidate.Runtime.HashOrderEntriesAppend
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashDelete_count_tail_words {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table order orderPos deletedPosition count lastSlot capacity used values : BitVec 64)
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
    (entries : HashValueEntriesWord used values capacity state)
    (occupancySeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ order + deletedPosition * 8 ∧
      panByteAlignHOL (used + slot) ≠ orderPos + lastSlot * 8 ∧ panByteAlignHOL (used + slot) ≠ table + 24)
    (valueSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      values + slot * 8 ≠ order + deletedPosition * 8 ∧ values + slot * 8 ≠ orderPos + lastSlot * 8 ∧ values + slot * 8 ≠ table + 24) :
    ∃ post, evaluateHOLFiniteState state hashDeleteCountTail = (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      post.clock = state.clock ∧ HashValueEntriesWord used values capacity post := by
  obtain ⟨post,run,ticks,_,_,domain,endian,memory,_⟩ := evaluate_hashDelete_count_tail state
    table order orderPos deletedPosition count lastSlot tableLocal orderLocal reverseLocal deletedLocal
    countDomain countCell loadDomain loadCell orderDomain reverseDomain
  have valid := entries.delete_final_writes state table order orderPos used values capacity count deletedPosition lastSlot occupancySeparate valueSeparate
  refine ⟨post,run,ticks,valid.after_read _ post used values capacity memory ?_ ?_⟩
  · classical
    split <;> exact domain
  · classical
    split <;> exact endian

#print axioms evaluate_hashDelete_count_tail_words
end InitECandidate.Runtime
