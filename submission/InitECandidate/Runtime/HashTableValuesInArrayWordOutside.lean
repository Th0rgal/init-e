import InitECandidate.Runtime.HashTablePhysicalStores
import InitECandidate.Runtime.HashTableReadyArrayWord
import InitECandidate.Runtime.HashTableValuesInPhysicalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- An array store preserves a table when its destination region misses all
live physical regions, without any enclosing-allocation separation. -/
theorem HashTableValuesIn.after_array_word_outside {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items base length index value : BitVec 64) (bits : Nat)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn table targets state)
    (inside : index.toNat < length.toNat) (aligned : base.toNat % 8 = 0)
    (bounded : base.toNat + length.toNat * 8 ≤ 33806089496)
    (separate : ∀ address : BitVec 64, base.toNat ≤ address.toNat → address.toNat < base.toNat + length.toNat * 8 →
      ¬tablePhysicalRegion table keys stride capacity used values order orderPos address) :
    HashTableValuesIn table targets
      (sourceWriteWord state (base + index * 8) value) := by
  have address := (hashFind_slot_address base index 8 length inside
    (by change base.toNat + length.toNat * 8 ≤ 33806089496; exact bounded) aligned (by decide)).1
  change (base + index * 8).toNat = base.toNat + index.toNat * 8 at address
  have product := Nat.mul_lt_mul_of_pos_right inside (by decide : 0 < 8)
  exact registered.after_word_outside state keyLength table keys stride capacity used values order orderPos items (base + index * 8) value bits ready.live.arrays targets
    (separate _ (by omega) (by omega))

#print axioms HashTableValuesIn.after_array_word_outside
end InitECandidate.Runtime
