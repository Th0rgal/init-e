import InitECandidate.Runtime.HashInsertLayout
import InitECandidate.Runtime.MemcpyIntervalFrame
namespace InitECandidate.Runtime
open Flapjack

/-- Every non-count header field precedes all insertion destinations in an
ordered table layout, including aligned copy-byte and occupancy stores. -/
theorem hashInsert_header_separation_width (table keys stride capacity used values order orderPos count keyLength : BitVec 64)
    (keysAligned : keys.toNat % 8 = 0) (strideAligned : stride.toNat % 8 = 0)
    (valuesAligned : values.toNat % 8 = 0) (usedAligned : used.toNat % 8 = 0)
    (orderAligned : order.toNat % 8 = 0) (orderPosAligned : orderPos.toNat % 8 = 0)
    (headerKeys : table.toNat + 72 ≤ keys.toNat)
    (headerValues : table.toNat + 72 ≤ values.toNat)
    (keysBefore : keys.toNat + capacity.toNat * stride.toNat ≤ used.toNat)
    (valuesBefore : values.toNat + capacity.toNat * 8 ≤ used.toNat)
    (usedBefore : used.toNat + capacity.toNat ≤ order.toNat)
    (orderBefore : order.toNat + capacity.toNat * 8 ≤ orderPos.toNat)
    (bounded : orderPos.toNat + capacity.toNat * 8 ≤ 33806089496)
    (fits : keyLength.toNat ≤ stride.toNat) (room : count.toNat < capacity.toNat)
    (offset : Nat) (field : offset ≤ 64) (notCount : offset ≠ 24) :
    let watched := table + BitVec.ofNat 64 offset
    (∀ slot : BitVec 64, slot.toNat < capacity.toNat → ∀ byte : Nat, byte < keyLength.toNat →
      watched ≠ keys + slot * stride + BitVec.ofNat 64 byte ∧
      watched ≠ panByteAlignHOL (keys + slot * stride + BitVec.ofNat 64 byte)) ∧
    (∀ slot : BitVec 64, slot.toNat < capacity.toNat → watched ≠ values + slot * 8 ∧
      watched ≠ panByteAlignHOL (used + slot) ∧ watched ≠ orderPos + slot * 8) ∧
    watched ≠ order + count * 8 ∧ watched ≠ table + 24 := by
  have natural : (BitVec.ofNat 64 offset).toNat = offset := by
    change offset % 2 ^ 64 = offset
    exact Nat.mod_eq_of_lt (by omega)
  have address : (table + BitVec.ofNat 64 offset).toNat = table.toNat + offset := by
    rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
  have wordLower : ∀ base : BitVec 64, base.toNat % 8 = 0 →
      base.toNat + capacity.toNat * 8 ≤ 33806089496 →
      ∀ index : BitVec 64, index.toNat < capacity.toNat → base.toNat ≤ (base + index * 8).toNat := by
    intro base aligned limit index inside
    have slot := hashFind_slot_address base index 8 capacity inside
      (by change base.toNat + capacity.toNat * 8 ≤ 33806089496; exact limit) aligned (by decide)
    change base.toNat ≤ (base + index * 8).toNat
    rw [slot.1]
    omega
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · intro slot inside
    have slotFacts := hashFind_slot_address keys slot stride capacity inside (by omega) keysAligned strideAligned
    have next := Nat.mul_le_mul_right stride.toNat (show slot.toNat + 1 ≤ capacity.toNat by omega)
    rw [Nat.add_mul,Nat.one_mul] at next
    apply memcpy_interval_separate (keys + slot * stride) keyLength (table + BitVec.ofNat 64 offset) slotFacts.2
      (by change (keys + slot * stride).toNat + keyLength.toNat ≤ 33806089496; omega)
    left
    omega
  · intro slot inside
    have valueLower := wordLower values valuesAligned (by omega) slot inside
    have reverseLower := wordLower orderPos orderPosAligned bounded slot inside
    have occupancy := hashOccupancy_aligned_interval used capacity slot usedAligned (by omega) inside
    refine ⟨?_,?_,?_⟩ <;> intro same <;>
      have equal := congrArg BitVec.toNat same <;> omega
  · have orderLower := wordLower order orderAligned (by omega) count room
    intro same
    have equal := congrArg BitVec.toNat same
    omega
  · have countAddress : (table + (24 : BitVec 64)).toNat = table.toNat + 24 := by
      rw [BitVec.toNat_add_of_lt (by change table.toNat + 24 < 2 ^ 64; omega)]
      rfl
    intro same
    have equal := congrArg BitVec.toNat same
    rw [address,countAddress] at equal
    omega

#print axioms hashInsert_header_separation_width
end InitECandidate.Runtime
