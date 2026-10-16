import InitECandidate.Runtime.HashInsertTableMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Ordered allocated table regions imply insertion's domains and separation
facts, without per-slot separation assumptions. -/
theorem hashInsert_table_memory_from_layout {F : Type}
    (capacity used table values order orderPos count : BitVec 64)
    (state : PanSemStateFiniteExact 64 F)
    (valuesAligned : values.toNat % 8 = 0) (usedAligned : used.toNat % 8 = 0)
    (orderAligned : order.toNat % 8 = 0) (orderPosAligned : orderPos.toNat % 8 = 0)
    (headerBefore : table.toNat + 72 ≤ values.toNat)
    (valuesBefore : values.toNat + capacity.toNat * 8 ≤ used.toNat)
    (usedBefore : used.toNat + capacity.toNat ≤ order.toNat)
    (orderBefore : order.toNat + capacity.toNat * 8 ≤ orderPos.toNat)
    (bounded : orderPos.toNat + capacity.toNat * 8 ≤ 33806089496)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < orderPos.toNat + capacity.toNat * 8 → state.memaddrs address)
    (valuesMemory : state.memory (table + 40) = .word values)
    (countMemory : state.memory (table + 24) = .word count)
    (agreement : count.toNat = hashOccupiedCount capacity (hashOccupancyRead state used))
    (room : count.toNat < capacity.toNat) :
    HashInsertTableMemory capacity used table values order orderPos count state := by
  have wordInterval : ∀ base : BitVec 64, base.toNat % 8 = 0 →
      base.toNat + capacity.toNat * 8 ≤ 33806089496 →
      ∀ index : BitVec 64, index.toNat < capacity.toNat →
        base.toNat ≤ (base + index * 8).toNat ∧
        (base + index * 8).toNat < base.toNat + capacity.toNat * 8 := by
    intro base aligned limit index inside
    have facts := hashFind_slot_offset base index 8 capacity 8 0 inside
      (by change base.toNat + capacity.toNat * 8 ≤ 33806089496; exact limit)
      aligned (by decide) (by decide) (by decide)
    simpa using facts.2
  have header : ∀ offset : Nat, offset ≤ 64 →
      (table + BitVec.ofNat 64 offset).toNat = table.toNat + offset := by
    intro offset small
    have natural : (BitVec.ofNat 64 offset).toNat = offset := by
      change offset % 2 ^ 64 = offset
      exact Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
  have v := wordInterval values valuesAligned (by omega)
  have o := wordInterval order orderAligned (by omega) count room
  have r := wordInterval orderPos orderPosAligned bounded
  have cells := fun index inside => hashOccupancy_aligned_interval used capacity index
    usedAligned (by omega) inside
  have h24 : (table + 24).toNat = table.toNat + 24 := header 24 (by decide)
  have h40 : (table + 40).toNat = table.toNat + 40 := header 40 (by decide)
  refine {
    valuesDomain := domain _ (by omega) (by omega)
    valuesMemory := valuesMemory
    valueDomain := ?_
    byteDomain := ?_
    orderDomain := domain _ (by omega) (by omega)
    orderPosDomain := ?_
    countDomain := domain _ (by omega) (by omega)
    countMemory := countMemory
    agreement := agreement
    noWrap := by omega
    valueCountSeparate := ?_
    valueSeparate := ?_
    separate := ?_
  }
  · intro index inside
    have interval := v index inside
    exact domain _ (by omega) (by omega)
  · intro index inside
    have interval := cells index inside
    exact domain _ (by omega) (by omega)
  · intro index inside
    have interval := r index inside
    exact domain _ (by omega) (by omega)
  · intro index inside same
    have interval := v index inside
    have equal := congrArg BitVec.toNat same
    omega
  · intro index inside slot slotInside same
    have vi := v index inside
    have ci := cells slot slotInside
    have equal := congrArg BitVec.toNat same
    omega
  · intro index inside slot slotInside
    have ri := r index inside
    have ci := cells slot slotInside
    refine ⟨?_,?_,?_⟩ <;> intro same <;>
      have equal := congrArg BitVec.toNat same <;> omega

#print axioms hashInsert_table_memory_from_layout
end InitECandidate.Runtime
