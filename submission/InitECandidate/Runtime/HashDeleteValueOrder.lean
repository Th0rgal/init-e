import InitECandidate.Runtime.HashDeleteValueTail
import InitECandidate.Runtime.HashOrderWordFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashDelete_value_order {F : Type} (state : PanSemStateFiniteExact 64 F)
    (values order orderPos hole scan position value used capacity items : BitVec 64)
    (valuesLocal : state.locals.lookup (ofString "vals") = some (.val (.word values)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (scanLocal : state.locals.lookup (ofString "j") = some (.val (.word scan)))
    (valueDomain : state.memaddrs (values + scan * 8))
    (valueCell : state.memory (values + scan * 8) = .word value)
    (destinationDomain : state.memaddrs (values + hole * 8))
    (loadDomain : state.memaddrs (orderPos + scan * 8))
    (loadCell : state.memory (orderPos + scan * 8) = .word position)
    (separate : orderPos + scan * 8 ≠ values + hole * 8)
    (orderDomain : state.memaddrs (order + position * 8))
    (reverseDomain : state.memaddrs (orderPos + hole * 8))
    (entries : HashOrderEntriesBound order capacity items state)
    (holeInside : hole.toNat < capacity.toNat)
    (valueSeparate : ∀ index : BitVec 64, index.toNat < items.toNat → order + index * 8 ≠ values + hole * 8)
    (orderSeparate : ∀ index : BitVec 64, index.toNat < items.toNat → order + index * 8 ≠ orderPos + hole * 8)
    (positionSeparate : order + position * 8 ≠ orderPos + hole * 8)
    (distinct : ∀ index : BitVec 64, index.toNat < items.toNat → index ≠ position →
      order + index * 8 ≠ order + position * 8) :
    ∃ post, evaluateHOLFiniteState state hashDeleteValueTail = (none,post) ∧
      post.clock = state.clock ∧ HashOrderEntriesBound order capacity items post := by
  have run := evaluate_hashDelete_value_tail state values order orderPos hole scan position value
    valuesLocal orderLocal reverseLocal holeLocal scanLocal valueDomain valueCell destinationDomain
    loadDomain loadCell separate orderDomain reverseDomain
  have valid := entries.value_move_stores state values order orderPos capacity items position hole value
    holeInside valueSeparate orderSeparate positionSeparate distinct
  rw [run]
  refine ⟨_,rfl,rfl,?_⟩
  exact valid.after_memory _ _ order capacity items rfl

#print axioms evaluate_hashDelete_value_order
end InitECandidate.Runtime
