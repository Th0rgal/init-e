import InitECandidate.Runtime.AllocationSeparation
import InitECandidate.Runtime.HashTableReadyWordOutside
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Byte stores update one aligned word; separation concerns that word. -/
theorem HashTableReady.after_byte_outside {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items address value cell : BitVec 64) (bits : Nat)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (outside : (panByteAlignHOL address).toNat < table.toNat ∨
      orderPos.toNat + capacity.toNat * 8 ≤ (panByteAlignHOL address).toNat) :
    HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer
      (sourceWriteByte state address value cell) := by
  exact ready.after_word_outside state keyLength table pointer keys stride capacity used values order orderPos items
    (panByteAlignHOL address)
    (panSetByteHOL address (BitVec.ofNat 64 (BitVec.ofNat 8 value.toNat).toNat) cell state.be) bits outside

/-- An occupancy byte store preserves a table disjoint from its byte array. -/
theorem HashTableReady.after_array_byte {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items base length index value cell : BitVec 64) (bits : Nat)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (inside : index.toNat < length.toNat) (aligned : base.toNat % 8 = 0)
    (bounded : base.toNat + length.toNat ≤ 2 ^ 64)
    (separate : base.toNat + length.toNat ≤ table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ base.toNat) :
    HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer
      (sourceWriteByte state (base + index) value cell) := by
  have interval := hashOccupancy_aligned_interval base length index aligned bounded inside
  apply ready.after_byte_outside state keyLength table pointer keys stride capacity used values order orderPos items (base + index) value cell bits
  rcases separate with before | after
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

#print axioms HashTableReady.after_byte_outside
#print axioms HashTableReady.after_array_byte
end InitECandidate.Runtime
