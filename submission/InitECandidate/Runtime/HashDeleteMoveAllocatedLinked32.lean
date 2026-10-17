import InitECandidate.Runtime.HashDeleteMoveAllocated32
import InitECandidate.Runtime.HashDeleteMoveLinked32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual deletion movement preserves linkage with memory access derived from table allocation. -/
theorem evaluate_hashDelete_move_allocated_linked32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keys stride hole scan values order orderPos used capacity items : BitVec 64)
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (scanLocal : state.locals.lookup (ofString "j") = some (.val (.word scan)))
    (sizeLocal : state.locals.lookup (ofString "klen") = some (.val (.word (32 : BitVec 64))))
    (table : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos items bits state)
    (scanInside : scan.toNat < capacity.toNat)
    (occupied : hashOccupancyRead state used scan ≠ some 0)
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (budget : 33 ≤ state.clock)
    (valuesLocal : state.locals.lookup (ofString "vals") = some (.val (.word values)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (entries : HashReverseEntriesBound used orderPos capacity items state)
    (holeInside : hole.toNat < capacity.toNat)
    (valueEntries : HashValueEntriesWord used values capacity state)
    (deletedPosition : BitVec 64) (different : scan ≠ hole)
    (linked : HashDeleteOrderLinked used order orderPos capacity items hole deletedPosition state)
 :
    ∃ post, evaluateHOLFiniteState state hashDeleteMoveBody = (none,post) ∧
      state.clock ≤ post.clock + 32 + 1 ∧ post.clock ≤ state.clock ∧
      HashDeleteOrderLinked used order orderPos capacity items scan deletedPosition post := by
  obtain ⟨value,valueCell⟩ := valueEntries scan scanInside occupied
  obtain ⟨position,loadCell,positionBound⟩ := entries scan scanInside occupied
  have bounds := invariant.delete_copy_bounds state table keys stride capacity used values order orderPos items hole scan bits holeInside scanInside
  have protectedCells := invariant.delete_copy_separate state table keys stride capacity used values order orderPos items hole scan bits holeInside scanInside keysBeforeValues
  have valueReverse := invariant.value_reverse_separate state table keys stride capacity used values order orderPos items hole bits holeInside
  have separate := valueReverse scan scanInside
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  have room := invariant.room
  have orderAddress : ∀ index : BitVec 64, index.toNat < capacity.toNat →
      (order + index * 8).toNat = order.toNat + index.toNat * 8 := by
    intro index inside
    exact (hashFind_slot_address order index 8 capacity inside
      (by change order.toNat + capacity.toNat * 8 ≤ 33806089496; omega) invariant.orderAligned (by decide)).1
  have facts := invariant.insertion_memory state table keys stride capacity used values order orderPos items bits
  have valueDomain := facts.valueDomain scan scanInside
  have destinationDomain := facts.valueDomain hole holeInside
  have hk := invariant.headerKeys
  have ku := invariant.keysBefore
  have uo := invariant.usedBefore
  have reverseAvailable : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → state.memaddrs (orderPos + slot * 8) := facts.orderPosDomain
  have loadDomain := reverseAvailable scan scanInside
  have reverseDomain := reverseAvailable hole holeInside
  have orderDomain : state.memaddrs (order + position * 8) := by
    have address := orderAddress position (Nat.lt_trans positionBound room)
    have product := Nat.mul_lt_mul_of_pos_right (Nat.lt_trans positionBound room) (by decide : 0 < 8)
    apply invariant.domain <;> omega
  obtain ⟨post,run,cost,remaining,postLinked⟩ := evaluate_hashDelete_move_linked32 state
    keys stride hole scan values order orderPos position value used capacity items
    keysLocal strideLocal holeLocal scanLocal sizeLocal bounds.small bounds.aligned bounds.sourceAligned budget
    bounds.wordDomain bounds.byteDomain bounds.sourceWordDomain bounds.sourceByteDomain protectedCells invariant.code
    valuesLocal orderLocal reverseLocal valueDomain valueCell destinationDomain loadDomain loadCell separate orderDomain reverseDomain
    table bits invariant holeInside scanInside deletedPosition different occupied linked
  exact ⟨post,run,cost,remaining,postLinked⟩

#print axioms evaluate_hashDelete_move_allocated_linked32
end InitECandidate.Runtime
