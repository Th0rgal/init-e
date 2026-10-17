import InitECandidate.Runtime.HashTablePhysicalStores
import InitECandidate.Runtime.HashTableReadyArrayWord
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- An array store preserves a table when its destination region misses all
live physical regions, without any enclosing-allocation separation. -/
theorem HashTableReady.after_array_word_physical {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items base length index value : BitVec 64) (bits : Nat)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (inside : index.toNat < length.toNat) (aligned : base.toNat % 8 = 0)
    (bounded : base.toNat + length.toNat * 8 ≤ 33806089496)
    (separate : ∀ address : BitVec 64, base.toNat ≤ address.toNat → address.toNat < base.toNat + length.toNat * 8 →
      ¬tablePhysicalRegion table keys stride capacity used values order orderPos address) :
    HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer
      (sourceWriteWord state (base + index * 8) value) := by
  have address := (hashFind_slot_address base index 8 length inside
    (by change base.toNat + length.toNat * 8 ≤ 33806089496; exact bounded) aligned (by decide)).1
  change (base + index * 8).toNat = base.toNat + index.toNat * 8 at address
  have product := Nat.mul_lt_mul_of_pos_right inside (by decide : 0 < 8)
  exact ready.after_word_physical state keyLength table pointer keys stride capacity used values order orderPos items (base + index * 8) value bits
    (separate _ (by omega) (by omega))

/-- The aligned word containing an occupancy byte stays within the byte array. -/
theorem HashTableReady.after_array_byte_physical {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items base length index value cell : BitVec 64) (bits : Nat)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (inside : index.toNat < length.toNat) (aligned : base.toNat % 8 = 0)
    (bounded : base.toNat + length.toNat ≤ 2 ^ 64)
    (separate : ∀ address : BitVec 64, base.toNat ≤ address.toNat → address.toNat < base.toNat + length.toNat →
      ¬tablePhysicalRegion table keys stride capacity used values order orderPos address) :
    HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer
      (sourceWriteByte state (base + index) value cell) := by
  have interval := hashOccupancy_aligned_interval base length index aligned bounded inside
  exact ready.after_byte_physical state keyLength table pointer keys stride capacity used values order orderPos items (base + index) value cell bits
    (separate _ interval.1 interval.2)

#print axioms HashTableReady.after_array_byte_physical

#print axioms HashTableReady.after_array_word_physical
end InitECandidate.Runtime
