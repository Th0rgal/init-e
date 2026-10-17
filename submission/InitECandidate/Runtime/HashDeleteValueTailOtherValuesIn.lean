import InitECandidate.Runtime.HashDeleteValueTail
import InitECandidate.Runtime.HashTablePhysicalArrayWord
import InitECandidate.Runtime.HashTableValuesInArrayWordOutside
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual deletion value and order movement preserves disjoint ready tables. -/
theorem evaluate_hashDelete_value_tail_other_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
    (values order orderPos hole scan position value : BitVec 64)
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
    (capacity : BitVec 64)
    (holeInside : hole.toNat < capacity.toNat) (positionInside : position.toNat < capacity.toNat)
    (valuesAligned : values.toNat % 8 = 0) (orderAligned : order.toNat % 8 = 0) (reverseAligned : orderPos.toNat % 8 = 0)
    (valuesBound : values.toNat + capacity.toNat * 8 ≤ 33806089496)
    (orderBound : order.toNat + capacity.toNat * 8 ≤ 33806089496)
    (reverseBound : orderPos.toNat + capacity.toNat * 8 ≤ 33806089496)
    (otherKeyLength table pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos items : BitVec 64) (bits : Nat)
    (ready : HashTableReady otherKeyLength table otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos items bits pointer state)
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn table targets state)
    (valuesSeparate : ∀ address : BitVec 64, values.toNat ≤ address.toNat → address.toNat < values.toNat + capacity.toNat * 8 →
      ¬tablePhysicalRegion table otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos address)
    (orderSeparate : ∀ address : BitVec 64, order.toNat ≤ address.toNat → address.toNat < order.toNat + capacity.toNat * 8 →
      ¬tablePhysicalRegion table otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos address)
    (reverseSeparate : ∀ address : BitVec 64, orderPos.toNat ≤ address.toNat → address.toNat < orderPos.toNat + capacity.toNat * 8 →
      ¬tablePhysicalRegion table otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos address) :
    ∃ post, evaluateHOLFiniteState state hashDeleteValueTail = (none,post) ∧
      HashTableReady otherKeyLength table otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos items bits pointer post ∧
      HashTableValuesIn table targets post ∧
      post.clock = state.clock ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have first := ready.after_array_word_physical state otherKeyLength table pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos items values capacity hole value bits
    holeInside valuesAligned valuesBound valuesSeparate
  let written := sourceWriteWord state (values + hole * 8) value
  let entered := setVarHOLFinite (ofString "moved_pos") (.val (.word position)) written
  have enteredReady := first.after_read written entered otherKeyLength table otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos items bits pointer rfl rfl rfl rfl rfl
  have second := enteredReady.after_array_word_physical entered otherKeyLength table pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos items order capacity position hole bits
    positionInside orderAligned orderBound orderSeparate
  have third := second.after_array_word_physical _ otherKeyLength table pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos items orderPos capacity hole position bits
    holeInside reverseAligned reverseBound reverseSeparate
  have firstValues := registered.after_array_word_outside state otherKeyLength table pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos items values capacity hole value bits ready targets
    holeInside valuesAligned valuesBound valuesSeparate
  have enteredValues : HashTableValuesIn table targets entered := firstValues.after_read rfl rfl rfl
  have secondValues := enteredValues.after_array_word_outside entered otherKeyLength table pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos items order capacity position hole bits enteredReady targets
    positionInside orderAligned orderBound orderSeparate
  have thirdValues := secondValues.after_array_word_outside _ otherKeyLength table pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos items orderPos capacity hole position bits second targets
    holeInside reverseAligned reverseBound reverseSeparate
  exact ⟨_,evaluate_hashDelete_value_tail state values order orderPos hole scan position value
    valuesLocal orderLocal reverseLocal holeLocal scanLocal valueDomain valueCell destinationDomain loadDomain loadCell separate orderDomain reverseDomain,
    third.after_read _ _ otherKeyLength table otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos items bits pointer rfl rfl rfl rfl rfl,
    thirdValues.after_read rfl rfl rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms evaluate_hashDelete_value_tail_other_values_in
end InitECandidate.Runtime
