import InitECandidate.Runtime.HashReverseMoveGeometry32
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Bounded reverse cells lie beyond occupancy, order entries, and the count
header; distinct in-range slots have distinct reverse addresses. -/
theorem HashTableArraysInvariant32.insert_reverse_separation {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count inserted : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (inside : inserted.toNat < capacity.toNat) :
    (orderPos + inserted * 8 ≠ table + 24) ∧
    (∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ inserted →
      orderPos + slot * 8 ≠ panByteAlignHOL (used + inserted) ∧
      orderPos + slot * 8 ≠ order + count * 8 ∧
      orderPos + slot * 8 ≠ orderPos + inserted * 8 ∧ orderPos + slot * 8 ≠ table + 24) := by
  have hk := invariant.headerKeys
  have ku := invariant.keysBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  have address : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      (orderPos + slot * 8).toNat = orderPos.toNat + slot.toNat * 8 := by
    intro slot bound
    exact (hashFind_slot_address orderPos slot 8 capacity bound
      (by change orderPos.toNat + capacity.toNat * 8 ≤ 33806089496; exact bounded)
      invariant.orderPosAligned (by decide)).1
  have header : (table + (24 : BitVec 64)).toNat = table.toNat + 24 := by
    rw [BitVec.toNat_add_of_lt (by change table.toNat + 24 < 2 ^ 64; omega)]
    rfl
  have headerSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → orderPos + slot * 8 ≠ table + 24 := by
    intro slot bound same
    have natural := congrArg BitVec.toNat same
    rw [address slot bound,header] at natural
    omega
  refine ⟨headerSeparate inserted inside,?_⟩
  intro slot bound different
  have stores := invariant.delete_reverse_separate state table keys stride capacity used values order orderPos count
    inserted count bits inside invariant.room slot bound different
  have occupancy := hashOccupancy_separate_allocation used capacity (orderPos + slot * 8)
    invariant.usedAligned (by omega) (Or.inr (by rw [address slot bound]; omega)) inserted inside
  exact ⟨Ne.symm occupancy,stores.1,stores.2,headerSeparate slot bound⟩

#print axioms HashTableArraysInvariant32.insert_reverse_separation
end InitECandidate.Runtime
