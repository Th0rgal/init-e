import InitECandidate.Runtime.HashDeleteValueTail
import InitECandidate.Runtime.HashValueMoveStores
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashDelete_value_words {F : Type} (state : PanSemStateFiniteExact 64 F)
    (values order orderPos hole scan position value used capacity : BitVec 64)
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
    (entries : HashValueEntriesWord used values capacity state)
    (valueOccupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ values + hole * 8)
    (distinct : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ hole →
      values + slot * 8 ≠ values + hole * 8)
    (orderOccupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ order + position * 8)
    (orderValues : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      values + slot * 8 ≠ order + position * 8)
    (reverseOccupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ orderPos + hole * 8)
    (reverseValues : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      values + slot * 8 ≠ orderPos + hole * 8) :
    ∃ post, evaluateHOLFiniteState state hashDeleteValueTail = (none,post) ∧
      post.clock = state.clock ∧ HashValueEntriesWord used values capacity post := by
  have run := evaluate_hashDelete_value_tail state values order orderPos hole scan position value
    valuesLocal orderLocal reverseLocal holeLocal scanLocal valueDomain valueCell destinationDomain
    loadDomain loadCell separate orderDomain reverseDomain
  have valid := entries.move_stores state used values order orderPos capacity hole position value
    valueOccupancy distinct orderOccupancy orderValues reverseOccupancy reverseValues
  rw [run]
  refine ⟨_,rfl,rfl,?_⟩
  exact valid.after_read _ _ used values capacity rfl rfl rfl

#print axioms evaluate_hashDelete_value_words
end InitECandidate.Runtime
