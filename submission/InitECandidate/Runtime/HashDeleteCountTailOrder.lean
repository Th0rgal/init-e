import InitECandidate.Runtime.HashDeleteCountTail
import InitECandidate.Runtime.HashDeleteFinalOrderBound
import InitECandidate.Runtime.HashOrderEntriesAppend
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashDelete_count_tail_order {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table order orderPos deletedPosition count lastSlot capacity : BitVec 64)
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
    (entries : HashOrderEntriesBound order capacity count state)
    (positive : 0 < count.toNat) (lastInside : lastSlot.toNat < capacity.toNat)
    (forwardSeparate : ∀ position : BitVec 64, position.toNat < count.toNat →
      order + position * 8 ≠ table + 24 ∧ order + position * 8 ≠ orderPos + lastSlot * 8 ∧
      (position ≠ deletedPosition → order + position * 8 ≠ order + deletedPosition * 8)) :
    ∃ post, evaluateHOLFiniteState state hashDeleteCountTail = (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      post.clock = state.clock ∧ HashOrderEntriesBound order capacity (count - 1) post := by
  obtain ⟨post,run,ticks,_,_,_,_,memory,_⟩ := evaluate_hashDelete_count_tail state
    table order orderPos deletedPosition count lastSlot tableLocal orderLocal reverseLocal deletedLocal
    countDomain countCell loadDomain loadCell orderDomain reverseDomain
  have valid := entries.delete_final_writes state table order orderPos capacity count deletedPosition lastSlot positive lastInside forwardSeparate
  exact ⟨post,run,ticks,valid.after_memory _ post order capacity (count - 1) memory⟩

#print axioms evaluate_hashDelete_count_tail_order
end InitECandidate.Runtime
