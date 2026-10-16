import InitECandidate.Runtime.HashTableArraysFind32
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Updating an in-range value preserves headers, domains and count agreement. -/
theorem HashTableArraysInvariant32.write_value {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count index value : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (inside : index.toNat < capacity.toNat) :
    HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits
      (sourceWriteWord state (values + index * 8) value) := by
  have va := invariant.valuesAligned
  have ua := invariant.usedAligned
  have hv := invariant.headerValues
  have vu := invariant.valuesBefore
  have uo := invariant.usedBefore
  have orr := invariant.orderBefore
  have limit := invariant.endBound
  have valueAddress := hashFind_slot_address values index 8 capacity inside
    (by change values.toNat + capacity.toNat * 8 ≤ 33806089496; omega) va (by decide)
  have headerSeparate : ∀ offset : Nat, offset ≤ 64 →
      table + BitVec.ofNat 64 offset ≠ values + index * 8 := by
    intro offset small
    have natural : (BitVec.ofNat 64 offset).toNat = offset := by
      change offset % 2 ^ 64 = offset
      exact Nat.mod_eq_of_lt (by omega)
    have address : (table + BitVec.ofNat 64 offset).toNat = table.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    intro same
    have equal := congrArg BitVec.toNat same
    rw [address,valueAddress.1] at equal
    omega
  have separate := hashSet_value_separate values used capacity index
    inside va ua vu (by omega)
  have preserved := sourceWriteWord_occupancy_preserved state capacity used
    (values + index * 8) value separate
  refine {
    code := invariant.code
    power := invariant.power
    keysAligned := invariant.keysAligned
    strideAligned := invariant.strideAligned
    valuesAligned := invariant.valuesAligned
    usedAligned := invariant.usedAligned
    orderAligned := invariant.orderAligned
    orderPosAligned := invariant.orderPosAligned
    headerKeys := invariant.headerKeys
    headerValues := invariant.headerValues
    keysBefore := invariant.keysBefore
    valuesBefore := invariant.valuesBefore
    usedBefore := invariant.usedBefore
    orderBefore := invariant.orderBefore
    endBound := invariant.endBound
    fits := invariant.fits
    domain := invariant.domain
    agreement := by rw [preserved]; exact invariant.agreement
    room := invariant.room
    cell0 := by
      simp only [sourceWriteWord]
      have different : table + (0 : BitVec 64) ≠ values + index * 8 := headerSeparate 0 (by decide)
      rw [if_neg different]
      exact invariant.cell0
    cell8 := by
      simp only [sourceWriteWord]
      have different : table + (8 : BitVec 64) ≠ values + index * 8 := headerSeparate 8 (by decide)
      rw [if_neg different]
      exact invariant.cell8
    cell16 := by
      simp only [sourceWriteWord]
      have different : table + (16 : BitVec 64) ≠ values + index * 8 := headerSeparate 16 (by decide)
      rw [if_neg different]
      exact invariant.cell16
    cell24 := by
      simp only [sourceWriteWord]
      have different : table + (24 : BitVec 64) ≠ values + index * 8 := headerSeparate 24 (by decide)
      rw [if_neg different]
      exact invariant.cell24
    cell32 := by
      simp only [sourceWriteWord]
      have different : table + (32 : BitVec 64) ≠ values + index * 8 := headerSeparate 32 (by decide)
      rw [if_neg different]
      exact invariant.cell32
    cell40 := by
      simp only [sourceWriteWord]
      have different : table + (40 : BitVec 64) ≠ values + index * 8 := headerSeparate 40 (by decide)
      rw [if_neg different]
      exact invariant.cell40
    cell48 := by
      simp only [sourceWriteWord]
      have different : table + (48 : BitVec 64) ≠ values + index * 8 := headerSeparate 48 (by decide)
      rw [if_neg different]
      exact invariant.cell48
    cell56 := by
      simp only [sourceWriteWord]
      have different : table + (56 : BitVec 64) ≠ values + index * 8 := headerSeparate 56 (by decide)
      rw [if_neg different]
      exact invariant.cell56
    cell64 := by
      simp only [sourceWriteWord]
      have different : table + (64 : BitVec 64) ≠ values + index * 8 := headerSeparate 64 (by decide)
      rw [if_neg different]
      exact invariant.cell64
  }

#print axioms HashTableArraysInvariant32.write_value
end InitECandidate.Runtime
