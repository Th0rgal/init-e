import InitECandidate.Runtime.HashDeleteCountTail
import InitECandidate.Runtime.HashTablePhysicalArrayWord
import InitECandidate.Runtime.HashTableValuesInArrayWordOutside
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Count-loading scopes and final deletion writes preserve a disjoint table. -/
theorem evaluate_hashDelete_count_tail_other_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table order orderPos deletedPosition count lastSlot : BitVec 64)
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
    (capacity : BitVec 64)
    (deletedInside : deletedPosition.toNat < capacity.toNat) (lastInside : lastSlot.toNat < capacity.toNat)
    (orderAligned : order.toNat % 8 = 0) (reverseAligned : orderPos.toNat % 8 = 0)
    (orderBound : order.toNat + capacity.toNat * 8 ≤ 33806089496)
    (reverseBound : orderPos.toNat + capacity.toNat * 8 ≤ 33806089496)
    (otherKeyLength otherTable pointer keys stride otherCapacity used values otherOrder otherOrderPos items : BitVec 64) (bits : Nat)
    (ready : HashTableReady otherKeyLength otherTable keys stride otherCapacity used values otherOrder otherOrderPos items bits pointer state)
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn otherTable targets state)
    (orderSeparate : ∀ address : BitVec 64, order.toNat ≤ address.toNat → address.toNat < order.toNat + capacity.toNat * 8 →
      ¬tablePhysicalRegion otherTable keys stride otherCapacity used values otherOrder otherOrderPos address)
    (reverseSeparate : ∀ address : BitVec 64, orderPos.toNat ≤ address.toNat → address.toNat < orderPos.toNat + capacity.toNat * 8 →
      ¬tablePhysicalRegion otherTable keys stride otherCapacity used values otherOrder otherOrderPos address)
    (countOutside : ¬tablePhysicalRegion otherTable keys stride otherCapacity used values otherOrder otherOrderPos (table + 24)) :
    ∃ post, evaluateHOLFiniteState state hashDeleteCountTail =
        (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      HashTableReady otherKeyLength otherTable keys stride otherCapacity used values otherOrder otherOrderPos items bits pointer post ∧
      HashTableValuesIn otherTable targets post ∧
      post.clock = state.clock ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  classical
  obtain ⟨post,run,clock,globals,code,domain,endian,memory,_⟩ :=
    evaluate_hashDelete_count_tail state table order orderPos deletedPosition count lastSlot
      tableLocal orderLocal reverseLocal deletedLocal countDomain countCell loadDomain loadCell orderDomain reverseDomain
  let swapped := if deletedPosition = count - 1 then state else
    sourceWriteWord (sourceWriteWord state (order + deletedPosition * 8) lastSlot) (orderPos + lastSlot * 8) deletedPosition
  have preserved : HashTableReady otherKeyLength otherTable keys stride otherCapacity used values otherOrder otherOrderPos items bits pointer swapped := by
    unfold swapped
    split
    · exact ready
    · have first := ready.after_array_word_physical state otherKeyLength otherTable pointer keys stride otherCapacity used values otherOrder otherOrderPos items order capacity deletedPosition lastSlot bits
        deletedInside orderAligned orderBound orderSeparate
      exact first.after_array_word_physical _ otherKeyLength otherTable pointer keys stride otherCapacity used values otherOrder otherOrderPos items orderPos capacity lastSlot deletedPosition bits
        lastInside reverseAligned reverseBound reverseSeparate
  have preservedValues : HashTableValuesIn otherTable targets swapped := by
    unfold swapped
    split
    · exact registered
    · have firstReady := ready.after_array_word_physical state otherKeyLength otherTable pointer keys stride otherCapacity used values otherOrder otherOrderPos items order capacity deletedPosition lastSlot bits
        deletedInside orderAligned orderBound orderSeparate
      have firstValues := registered.after_array_word_outside state otherKeyLength otherTable pointer keys stride otherCapacity used values otherOrder otherOrderPos items order capacity deletedPosition lastSlot bits ready targets
        deletedInside orderAligned orderBound orderSeparate
      exact firstValues.after_array_word_outside _ otherKeyLength otherTable pointer keys stride otherCapacity used values otherOrder otherOrderPos items orderPos capacity lastSlot deletedPosition bits firstReady targets
        lastInside reverseAligned reverseBound reverseSeparate
  have writtenValues := preservedValues.after_word_outside swapped otherKeyLength otherTable keys stride otherCapacity used values otherOrder otherOrderPos items (table + 24) (count - 1) bits preserved.live.arrays targets countOutside
  have written := preserved.after_word_physical swapped otherKeyLength otherTable pointer keys stride otherCapacity used values otherOrder otherOrderPos items (table + 24) (count - 1) bits countOutside
  have swappedGlobals : swapped.globals = state.globals := by unfold swapped; split <;> rfl
  have swappedCode : swapped.code = state.code := by unfold swapped; split <;> rfl
  have swappedDomain : swapped.memaddrs = state.memaddrs := by unfold swapped; split <;> rfl
  have swappedEndian : swapped.be = state.be := by unfold swapped; split <;> rfl
  refine ⟨post,run,?_,?_,clock,globals,code,domain,endian⟩
  · exact written.after_read _ post otherKeyLength otherTable keys stride otherCapacity used values otherOrder otherOrderPos items bits pointer memory
      (globals.trans swappedGlobals.symm) (code.trans swappedCode.symm)
      (domain.trans swappedDomain.symm) (endian.trans swappedEndian.symm)
  · exact writtenValues.after_read memory (domain.trans swappedDomain.symm) (endian.trans swappedEndian.symm)

#print axioms evaluate_hashDelete_count_tail_other_values_in
end InitECandidate.Runtime
