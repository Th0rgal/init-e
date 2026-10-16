import InitECandidate.Runtime.HashDeleteValueTail
import InitECandidate.Runtime.HashOccupancyPreservation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashDelete_value_occupancy {F : Type} (state : PanSemStateFiniteExact 64 F)
    (values order orderPos hole scan position value capacity used : BitVec 64)
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
    (occupancySeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ values + hole * 8 ∧
      panByteAlignHOL (used + slot) ≠ order + position * 8 ∧
      panByteAlignHOL (used + slot) ≠ orderPos + hole * 8) :
    ∃ post, evaluateHOLFiniteState state hashDeleteValueTail = (none,post) ∧
      post.clock = state.clock ∧
      (∀ slot : BitVec 64, slot.toNat < capacity.toNat →
        hashOccupancyRead post used slot = hashOccupancyRead state used slot) := by
  have run := evaluate_hashDelete_value_tail state values order orderPos hole scan position value
    valuesLocal orderLocal reverseLocal holeLocal scanLocal valueDomain valueCell destinationDomain
    loadDomain loadCell separate orderDomain reverseDomain
  rw [run]
  refine ⟨_,rfl,rfl,?_⟩
  intro slot inside
  have disjoint := occupancySeparate slot inside
  have valueSeparate : panByteAlignHOL (used + slot) ≠ values + hole * 8#64 := disjoint.1
  have orderSeparate : panByteAlignHOL (used + slot) ≠ order + position * 8#64 := disjoint.2.1
  have reverseSeparate : panByteAlignHOL (used + slot) ≠ orderPos + hole * 8#64 := disjoint.2.2
  simp [hashOccupancyRead,panMemLoadByteHOL,sourceWriteWord,setVarHOLFinite,
    valueSeparate,orderSeparate,reverseSeparate]
  rfl

#print axioms evaluate_hashDelete_value_occupancy
end InitECandidate.Runtime
