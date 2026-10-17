import InitECandidate.Runtime.HashDeleteFinalStores
import InitECandidate.Runtime.HashTableReadyArrayWord32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original final swap, count store and return preserve disjoint ready tables. -/
theorem evaluate_hashDelete_final_stores_other {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table order orderPos deletedPosition lastPosition lastSlot : BitVec 64)
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (deletedLocal : state.locals.lookup (ofString "deleted_pos") = some (.val (.word deletedPosition)))
    (lastLocal : state.locals.lookup (ofString "last_pos") = some (.val (.word lastPosition)))
    (loadDomain : state.memaddrs (order + lastPosition * 8))
    (loadCell : state.memory (order + lastPosition * 8) = .word lastSlot)
    (orderDomain : state.memaddrs (order + deletedPosition * 8))
    (reverseDomain : state.memaddrs (orderPos + lastSlot * 8))
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (countDomain : state.memaddrs (table + 24))
    (capacity : BitVec 64)
    (deletedInside : deletedPosition.toNat < capacity.toNat) (lastInside : lastSlot.toNat < capacity.toNat)
    (orderAligned : order.toNat % 8 = 0) (reverseAligned : orderPos.toNat % 8 = 0)
    (orderBound : order.toNat + capacity.toNat * 8 ≤ 33806089496)
    (reverseBound : orderPos.toNat + capacity.toNat * 8 ≤ 33806089496)
    (otherTable pointer keys stride otherCapacity used values otherOrder otherOrderPos items : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 otherTable keys stride otherCapacity used values otherOrder otherOrderPos items bits pointer state)
    (orderSeparate : order.toNat + capacity.toNat * 8 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ order.toNat)
    (reverseSeparate : orderPos.toNat + capacity.toNat * 8 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ orderPos.toNat)
    (countOutside : (table + 24).toNat < otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ (table + 24).toNat) :
    ∃ post, evaluateHOLFiniteState state hashDeleteFinalStores =
        (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      HashTableReady32 otherTable keys stride otherCapacity used values otherOrder otherOrderPos items bits pointer post ∧
      post.clock = state.clock ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  classical
  let swapped := if deletedPosition = lastPosition then state else
    sourceWriteWord (sourceWriteWord state (order + deletedPosition * 8) lastSlot) (orderPos + lastSlot * 8) deletedPosition
  have preserved : HashTableReady32 otherTable keys stride otherCapacity used values otherOrder otherOrderPos items bits pointer swapped := by
    unfold swapped
    split
    · exact ready
    · have first := ready.after_array_word state otherTable pointer keys stride otherCapacity used values otherOrder otherOrderPos items order capacity deletedPosition lastSlot bits
        deletedInside orderAligned orderBound orderSeparate
      exact first.after_array_word _ otherTable pointer keys stride otherCapacity used values otherOrder otherOrderPos items orderPos capacity lastSlot deletedPosition bits
        lastInside reverseAligned reverseBound reverseSeparate
  have written := preserved.after_word_outside swapped otherTable pointer keys stride otherCapacity used values otherOrder otherOrderPos items (table + 24) lastPosition bits countOutside
  have clock : swapped.clock = state.clock := by unfold swapped; split <;> rfl
  have globals : swapped.globals = state.globals := by unfold swapped; split <;> rfl
  have code : swapped.code = state.code := by unfold swapped; split <;> rfl
  have domain : swapped.memaddrs = state.memaddrs := by unfold swapped; split <;> rfl
  have endian : swapped.be = state.be := by unfold swapped; split <;> rfl
  exact ⟨_,evaluate_hashDelete_final_stores state table order orderPos deletedPosition lastPosition lastSlot
    orderLocal reverseLocal deletedLocal lastLocal loadDomain loadCell orderDomain reverseDomain tableLocal countDomain,
    written.after_read _ _ otherTable keys stride otherCapacity used values otherOrder otherOrderPos items bits pointer rfl rfl rfl rfl rfl,
    clock,globals,code,domain,endian⟩

#print axioms evaluate_hashDelete_final_stores_other
end InitECandidate.Runtime
