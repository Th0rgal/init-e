import InitECandidate.Runtime.HashOrderEntriesAppend
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Ordered, bounded allocations separate live order entries from the reverse
index and header count, and distinguish the appended entry from older ones. -/
theorem hashOrder_bookkeeping_separation
    (table order orderPos capacity items slot : BitVec 64)
    (orderAligned : order.toNat % 8 = 0)
    (reverseAligned : orderPos.toNat % 8 = 0)
    (headerBefore : table.toNat + 72 ≤ order.toNat)
    (orderBefore : order.toNat + capacity.toNat * 8 ≤ orderPos.toNat)
    (bounded : orderPos.toNat + capacity.toNat * 8 ≤ 33806089496)
    (room : items.toNat < capacity.toNat) (inside : slot.toNat < capacity.toNat) :
    (∀ position : BitVec 64, position.toNat ≤ items.toNat →
      order + position * 8 ≠ orderPos + slot * 8 ∧ order + position * 8 ≠ table + 24) ∧
    (∀ position : BitVec 64, position.toNat < items.toNat →
      order + position * 8 ≠ order + items * 8) := by
  have entry : ∀ position : BitVec 64, position.toNat ≤ items.toNat →
      (order + position * 8).toNat = order.toNat + position.toNat * 8 := by
    intro position before
    exact (hashFind_slot_address order position 8 capacity (by omega)
      (by change order.toNat + capacity.toNat * 8 ≤ 33806089496; omega)
      orderAligned (by decide)).1
  have reverse := (hashFind_slot_address orderPos slot 8 capacity inside
    (by change orderPos.toNat + capacity.toNat * 8 ≤ 33806089496; exact bounded)
    reverseAligned (by decide)).1
  have header : (table + (24 : BitVec 64)).toNat = table.toNat + 24 := by
    rw [BitVec.toNat_add_of_lt (by change table.toNat + 24 < 2 ^ 64; omega)]
    rfl
  constructor
  · intro position before
    have address := entry position before
    have upper := Nat.mul_lt_mul_of_pos_right (show position.toNat < capacity.toNat by omega) (by decide : 0 < 8)
    constructor <;> intro same <;> have equal := congrArg BitVec.toNat same
    · rw [address,reverse] at equal
      omega
    · rw [address,header] at equal
      omega
  · intro position before same
    have left := entry position (by omega)
    have right := entry items (by omega)
    have equal := congrArg BitVec.toNat same
    rw [left,right] at equal
    omega

/-- Concrete layout facts discharge all bookkeeping aliasing obligations. -/
theorem HashOrderEntriesBound.bookkeeping_layout {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table order orderPos capacity items slot : BitVec 64)
    (entries : HashOrderEntriesBound order capacity items state)
    (orderAligned : order.toNat % 8 = 0)
    (reverseAligned : orderPos.toNat % 8 = 0)
    (headerBefore : table.toNat + 72 ≤ order.toNat)
    (orderBefore : order.toNat + capacity.toNat * 8 ≤ orderPos.toNat)
    (bounded : orderPos.toNat + capacity.toNat * 8 ≤ 33806089496)
    (room : items.toNat < capacity.toNat) (inside : slot.toNat < capacity.toNat) :
    HashOrderEntriesBound order capacity (items + 1)
      (sourceWriteWord (sourceWriteWord (sourceWriteWord state
        (order + items * 8) slot) (orderPos + slot * 8) items) (table + 24) (items + 1)) := by
  have separation := hashOrder_bookkeeping_separation table order orderPos capacity items slot
    orderAligned reverseAligned headerBefore orderBefore bounded room inside
  have capBound := capacity.isLt
  exact entries.bookkeeping state table order orderPos capacity items slot (by omega) inside separation.1 separation.2

#print axioms HashOrderEntriesBound.bookkeeping_layout
#print axioms hashOrder_bookkeeping_separation
end InitECandidate.Runtime
