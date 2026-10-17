import InitECandidate.Runtime.HashTableReadyFrame
import InitECandidate.Runtime.AllocationSeparation
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Preserving memory throughout the table allocation retains every runtime
fact even when unrelated heap cells and locals change. -/
theorem HashTableReady.interval_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items : BitVec 64) (bits : Nat)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (frame : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < orderPos.toNat + capacity.toNat * 8 → post.memory address = state.memory address)
    (globals : post.globals = state.globals) (code : post.code = state.code)
    (domain : post.memaddrs = state.memaddrs) (endian : post.be = state.be) :
    HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer post := by
  have hv := ready.live.arrays.headerValues
  have vu := ready.live.arrays.valuesBefore
  have uo := ready.live.arrays.usedBefore
  have oo := ready.live.arrays.orderBefore
  have bounded := ready.live.arrays.endBound
  have room := ready.live.arrays.room
  have array : ∀ base : BitVec 64, table.toNat ≤ base.toNat →
      base.toNat + capacity.toNat * 8 ≤ orderPos.toNat + capacity.toNat * 8 → base.toNat % 8 = 0 →
      ∀ slot : BitVec 64, slot.toNat < capacity.toNat → post.memory (base + slot * 8) = state.memory (base + slot * 8) := by
    intro base lower upper aligned slot inside
    have address := (hashFind_slot_address base slot 8 capacity inside
      (by change base.toNat + capacity.toNat * 8 ≤ 33806089496; omega) aligned (by decide)).1
    change (base + slot * 8).toNat = base.toNat + slot.toNat * 8 at address
    have product := Nat.mul_lt_mul_of_pos_right inside (by decide : 0 < 8)
    apply frame <;> omega
  apply ready.framed state post keyLength table pointer keys stride capacity used values order orderPos items bits
  · intro offset member
    have small : offset ≤ 64 := by simp at member; omega
    have natural : (BitVec.ofNat 64 offset).toNat = offset := by
      change offset % 2 ^ 64 = offset
      exact Nat.mod_eq_of_lt (by omega)
    have address : (table + BitVec.ofNat 64 offset).toNat = table.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    apply frame <;> omega
  · intro slot inside
    have interval := hashOccupancy_aligned_interval used capacity slot ready.live.arrays.usedAligned (by omega) inside
    have cell := frame (panByteAlignHOL (used + slot)) (by omega) (by omega)
    simp only [hashOccupancyRead,panMemLoadByteHOL,endian,cell]
    rw [domain]
  · exact array values (by omega) (by omega) ready.live.arrays.valuesAligned
  · exact array orderPos (by omega) (by omega) ready.live.arrays.orderPosAligned
  · intro position inside
    exact array order (by omega) (by omega) ready.live.arrays.orderAligned position (by omega)
  · exact globals
  · exact code
  · exact domain

#print axioms HashTableReady.interval_frame
end InitECandidate.Runtime
