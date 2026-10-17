import InitECandidate.Runtime.HashTableReadyWord32
import InitECandidate.Runtime.AllocationSeparation
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A word write outside the table allocation preserves the complete runtime
state, including writes to journal regions allocated earlier or later. -/
theorem HashTableReady32.after_word_outside {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items destination value : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (outside : destination.toNat < table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ destination.toNat) :
    HashTableReady32 table keys stride capacity used values order orderPos items bits pointer
      (sourceWriteWord state destination value) := by
  have hv := ready.live.arrays.headerValues
  have vu := ready.live.arrays.valuesBefore
  have uo := ready.live.arrays.usedBefore
  have oo := ready.live.arrays.orderBefore
  have bounded := ready.live.arrays.endBound
  have room := ready.live.arrays.room
  have distinct : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < orderPos.toNat + capacity.toNat * 8 → address ≠ destination := by
    intro address lower upper same
    have equal := congrArg BitVec.toNat same
    rcases outside with before | after <;> omega
  have array : ∀ base : BitVec 64, table.toNat ≤ base.toNat →
      base.toNat + capacity.toNat * 8 ≤ orderPos.toNat + capacity.toNat * 8 → base.toNat % 8 = 0 →
      ∀ slot : BitVec 64, slot.toNat < capacity.toNat → base + slot * 8 ≠ destination := by
    intro base lower upper aligned slot inside
    have address := (hashFind_slot_address base slot 8 capacity inside
      (by change base.toNat + capacity.toNat * 8 ≤ 33806089496; omega) aligned (by decide)).1
    change (base + slot * 8).toNat = base.toNat + slot.toNat * 8 at address
    have product := Nat.mul_lt_mul_of_pos_right inside (by decide : 0 < 8)
    apply distinct <;> omega
  apply ready.after_word state table pointer keys stride capacity used values order orderPos items destination value bits
  · intro offset member
    have small : offset ≤ 64 := by simp at member; omega
    have natural : (BitVec.ofNat 64 offset).toNat = offset := by
      change offset % 2 ^ 64 = offset
      exact Nat.mod_eq_of_lt (by omega)
    have address : (table + BitVec.ofNat 64 offset).toNat = table.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    apply distinct <;> omega
  · intro slot inside
    have interval := hashOccupancy_aligned_interval used capacity slot ready.live.arrays.usedAligned (by omega) inside
    apply distinct <;> omega
  · exact array values (by omega) (by omega) ready.live.arrays.valuesAligned
  · exact array orderPos (by omega) (by omega) ready.live.arrays.orderPosAligned
  · intro position inside
    exact array order (by omega) (by omega) ready.live.arrays.orderAligned position (by omega)

#print axioms HashTableReady32.after_word_outside
end InitECandidate.Runtime
