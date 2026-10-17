import InitECandidate.Runtime.HashDeleteMoveStores
import InitECandidate.Runtime.HashTableReadyArrayWord32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual deletion movement stores preserve a table disjoint from both order arrays. -/
theorem evaluate_hashDelete_move_stores_other {F : Type} (state : PanSemStateFiniteExact 64 F)
    (order orderPos capacity hole scan position : BitVec 64)
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (scanLocal : state.locals.lookup (ofString "j") = some (.val (.word scan)))
    (positionLocal : state.locals.lookup (ofString "moved_pos") = some (.val (.word position)))
    (orderDomain : state.memaddrs (order + position * 8)) (reverseDomain : state.memaddrs (orderPos + hole * 8))
    (holeInside : hole.toNat < capacity.toNat) (positionInside : position.toNat < capacity.toNat)
    (orderAligned : order.toNat % 8 = 0) (reverseAligned : orderPos.toNat % 8 = 0)
    (orderBound : order.toNat + capacity.toNat * 8 ≤ 33806089496) (reverseBound : orderPos.toNat + capacity.toNat * 8 ≤ 33806089496)
    (table pointer keys stride otherCapacity used values otherOrder otherOrderPos items : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride otherCapacity used values otherOrder otherOrderPos items bits pointer state)
    (orderSeparate : order.toNat + capacity.toNat * 8 ≤ table.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ order.toNat)
    (reverseSeparate : orderPos.toNat + capacity.toNat * 8 ≤ table.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ orderPos.toNat) :
    ∃ post, evaluateHOLFiniteState state hashDeleteMoveStores = (none,post) ∧
      HashTableReady32 table keys stride otherCapacity used values otherOrder otherOrderPos items bits pointer post ∧
      post.clock = state.clock ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have first := ready.after_array_word state table pointer keys stride otherCapacity used values otherOrder otherOrderPos items order capacity position hole bits
    positionInside orderAligned orderBound orderSeparate
  have second := first.after_array_word _ table pointer keys stride otherCapacity used values otherOrder otherOrderPos items orderPos capacity hole position bits
    holeInside reverseAligned reverseBound reverseSeparate
  exact ⟨_,evaluate_hashDelete_move_stores state order orderPos hole scan position orderLocal reverseLocal holeLocal scanLocal positionLocal orderDomain reverseDomain,
    second.after_read _ _ table keys stride otherCapacity used values otherOrder otherOrderPos items bits pointer rfl rfl rfl rfl rfl,
    rfl,rfl,rfl,rfl,rfl⟩

#print axioms evaluate_hashDelete_move_stores_other
end InitECandidate.Runtime
