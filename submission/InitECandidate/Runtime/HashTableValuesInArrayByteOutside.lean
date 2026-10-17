import InitECandidate.Runtime.HashTableValuesInPhysicalFrame
import InitECandidate.Runtime.HashTablePhysicalArrayWord
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Clearing an occupancy byte outside a watched table preserves its registered values. -/
theorem HashTableValuesIn.after_array_byte_outside {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items base length index value cell : BitVec 64) (bits : Nat)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn table targets state)
    (inside : index.toNat < length.toNat) (aligned : base.toNat % 8 = 0)
    (bounded : base.toNat + length.toNat ≤ 2 ^ 64)
    (separate : ∀ address : BitVec 64, base.toNat ≤ address.toNat → address.toNat < base.toNat + length.toNat →
      ¬tablePhysicalRegion table keys stride capacity used values order orderPos address) :
    HashTableValuesIn table targets (sourceWriteByte state (base + index) value cell) := by
  have interval := hashOccupancy_aligned_interval base length index aligned bounded inside
  apply registered.physical_frame state _ keyLength table keys stride capacity used values order orderPos items bits ready.live.arrays targets
  · intro address member
    apply sourceWriteByte_memory_other
    intro same
    apply separate _ interval.1 interval.2
    rw [← same]
    exact member
  · rfl
  · rfl

#print axioms HashTableValuesIn.after_array_byte_outside
end InitECandidate.Runtime
