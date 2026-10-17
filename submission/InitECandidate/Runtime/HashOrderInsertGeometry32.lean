import InitECandidate.Runtime.HashOrderLinkedInsertStores
import InitECandidate.Runtime.HashTableArraysFind32
import InitECandidate.Runtime.HashReverseInsertGeometry32
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Forward order cells precede the reverse array, follow occupancy and the
header, and distinguish all live positions from the appended count position. -/
theorem HashTableArraysInvariant32.insert_order_separation {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos items inserted : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos items bits state)
    (inside : inserted.toNat < capacity.toNat) :
    (order + items * 8 ≠ orderPos + inserted * 8 ∧ order + items * 8 ≠ table + 24) ∧
    (∀ position : BitVec 64, position.toNat < items.toNat →
      order + position * 8 ≠ panByteAlignHOL (used + inserted) ∧
      order + position * 8 ≠ order + items * 8 ∧
      order + position * 8 ≠ orderPos + inserted * 8 ∧ order + position * 8 ≠ table + 24) := by
  have hk := invariant.headerKeys
  have ku := invariant.keysBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  have room := invariant.room
  have address : ∀ position : BitVec 64, position.toNat < capacity.toNat →
      (order + position * 8).toNat = order.toNat + position.toNat * 8 := by
    intro position bound
    exact (hashFind_slot_address order position 8 capacity bound
      (by change order.toNat + capacity.toNat * 8 ≤ 33806089496; omega) invariant.orderAligned (by decide)).1
  have ra := (hashFind_slot_address orderPos inserted 8 capacity inside
    (by change orderPos.toNat + capacity.toNat * 8 ≤ 33806089496; exact bounded) invariant.orderPosAligned (by decide)).1
  change (orderPos + inserted * 8).toNat = orderPos.toNat + inserted.toNat * 8 at ra
  have ha : (table + (24 : BitVec 64)).toNat = table.toNat + 24 := by
    rw [BitVec.toNat_add_of_lt (by change table.toNat + 24 < 2 ^ 64; omega)]
    rfl
  have separate : ∀ position : BitVec 64, position.toNat < capacity.toNat →
      order + position * 8 ≠ orderPos + inserted * 8 ∧ order + position * 8 ≠ table + 24 := by
    intro position bound
    have oa := address position bound
    have product := Nat.mul_lt_mul_of_pos_right bound (by decide : 0 < 8)
    constructor <;> intro same <;> have natural := congrArg BitVec.toNat same
    · rw [oa,ra] at natural; omega
    · rw [oa,ha] at natural; omega
  refine ⟨separate items room,?_⟩
  intro position before
  have inRange := Nat.lt_trans before room
  have occupancy := hashOccupancy_separate_allocation used capacity (order + position * 8)
    invariant.usedAligned (by omega) (Or.inr (by rw [address position inRange]; omega)) inserted inside
  refine ⟨Ne.symm occupancy,?_,separate position inRange⟩
  intro same
  have natural := congrArg BitVec.toNat same
  rw [address position inRange,address items room] at natural
  omega

theorem HashOrderLinked.insert_stores_layout32 {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos items inserted cell : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos items bits state)
    (linked : HashOrderLinked used order orderPos capacity items state)
    (inside : inserted.toNat < capacity.toNat)
    (cellMemory : state.memory (panByteAlignHOL (used + inserted)) = .word cell) :
    HashOrderLinked used order orderPos capacity (items + 1)
      (sourceWriteWord (sourceWriteWord (sourceWriteWord
        (sourceWriteByte state (used + inserted) 1 cell) (order + items * 8) inserted)
        (orderPos + inserted * 8) items) (table + 24) (items + 1)) := by
  have facts := invariant.insertion_memory state table keys stride capacity used values order orderPos items bits
  obtain ⟨newForward,forward⟩ := invariant.insert_order_separation state table keys stride capacity used values order orderPos items inserted bits inside
  obtain ⟨newReverse,reverse⟩ := invariant.insert_reverse_separation state table keys stride capacity used values order orderPos items inserted bits inside
  exact linked.insert_stores state used order orderPos capacity items inserted table cell facts.noWrap cellMemory
    newForward forward newReverse (facts.separate inserted inside) reverse

#print axioms HashOrderLinked.insert_stores_layout32

#print axioms HashTableArraysInvariant32.insert_order_separation
end InitECandidate.Runtime
