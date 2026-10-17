import InitECandidate.Runtime.HashTableReadyIntervalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Live physical regions of a table, allowing gaps after array relocation. -/
def tablePhysicalRegion (table keys stride capacity used values order orderPos address : BitVec 64) : Prop :=
  (table.toNat ≤ address.toNat ∧ address.toNat < table.toNat + 72) ∨
  (keys.toNat ≤ address.toNat ∧ address.toNat < keys.toNat + capacity.toNat * stride.toNat) ∨
  (used.toNat ≤ address.toNat ∧ address.toNat < used.toNat + capacity.toNat) ∨
  (values.toNat ≤ address.toNat ∧ address.toNat < values.toNat + capacity.toNat * 8) ∨
  (order.toNat ≤ address.toNat ∧ address.toNat < order.toNat + capacity.toNat * 8) ∨
  (orderPos.toNat ≤ address.toNat ∧ address.toNat < orderPos.toNat + capacity.toNat * 8)

/-- Only live regions need to remain intact; writes in gaps are harmless. -/
theorem HashTableReady.physical_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items : BitVec 64) (bits : Nat)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (frame : ∀ address : BitVec 64, tablePhysicalRegion table keys stride capacity used values order orderPos address →
      post.memory address = state.memory address)
    (globals : post.globals = state.globals) (code : post.code = state.code)
    (domain : post.memaddrs = state.memaddrs) (endian : post.be = state.be) :
    HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer post := by
  have hk := ready.live.arrays.headerKeys
  have ku := ready.live.arrays.keysBefore
  have vu := ready.live.arrays.valuesBefore
  have uo := ready.live.arrays.usedBefore
  have oo := ready.live.arrays.orderBefore
  have limit := ready.live.arrays.endBound
  have room := ready.live.arrays.room
  have array : ∀ base : BitVec 64, base.toNat % 8 = 0 → base.toNat + capacity.toNat * 8 ≤ 33806089496 →
      (∀ address : BitVec 64, base.toNat ≤ address.toNat → address.toNat < base.toNat + capacity.toNat * 8 →
        tablePhysicalRegion table keys stride capacity used values order orderPos address) →
      ∀ slot : BitVec 64, slot.toNat < capacity.toNat → post.memory (base + slot * 8) = state.memory (base + slot * 8) := by
    intro base aligned bound region slot inside
    have address := (hashFind_slot_address base slot 8 capacity inside
      (by change base.toNat + capacity.toNat * 8 ≤ 33806089496; exact bound) aligned (by decide)).1
    change (base + slot * 8).toNat = base.toNat + slot.toNat * 8 at address
    have product := Nat.mul_lt_mul_of_pos_right inside (by decide : 0 < 8)
    exact frame _ (region _ (by omega) (by omega))
  apply ready.framed state post keyLength table pointer keys stride capacity used values order orderPos items bits
  · intro offset member
    have small : offset ≤ 64 := by simp at member; omega
    have natural : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
    have address : (table + BitVec.ofNat 64 offset).toNat = table.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    apply frame
    exact Or.inl ⟨by omega,by omega⟩
  · intro slot inside
    have interval := hashOccupancy_aligned_interval used capacity slot ready.live.arrays.usedAligned (by omega) inside
    have cell := frame (panByteAlignHOL (used + slot)) (by unfold tablePhysicalRegion; omega)
    simp only [hashOccupancyRead,panMemLoadByteHOL,endian,cell]
    rw [domain]
  · exact array values ready.live.arrays.valuesAligned (by omega) (by intro address lower upper; unfold tablePhysicalRegion; omega)
  · exact array orderPos ready.live.arrays.orderPosAligned limit (by intro address lower upper; unfold tablePhysicalRegion; omega)
  · intro position inside
    exact array order ready.live.arrays.orderAligned (by omega) (by intro address lower upper; unfold tablePhysicalRegion; omega) position (by omega)
  · exact globals
  · exact code
  · exact domain

#print axioms HashTableReady.physical_frame
end InitECandidate.Runtime
