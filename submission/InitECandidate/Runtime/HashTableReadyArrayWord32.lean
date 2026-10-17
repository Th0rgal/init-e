import InitECandidate.Runtime.HashTableReadyWordOutside32
import InitECandidate.Runtime.HashFindArguments
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- An indexed array word store preserves a table disjoint from that array. -/
theorem HashTableReady32.after_array_word {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items base length index value : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (inside : index.toNat < length.toNat) (aligned : base.toNat % 8 = 0)
    (bounded : base.toNat + length.toNat * 8 ≤ 33806089496)
    (separate : base.toNat + length.toNat * 8 ≤ table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ base.toNat) :
    HashTableReady32 table keys stride capacity used values order orderPos items bits pointer
      (sourceWriteWord state (base + index * 8) value) := by
  have address := (hashFind_slot_address base index 8 length inside (by simpa using bounded) aligned (by decide)).1
  change (base + index * 8).toNat = base.toNat + index.toNat * 8 at address
  have product := Nat.mul_lt_mul_of_pos_right inside (by decide : 0 < 8)
  apply ready.after_word_outside state table pointer keys stride capacity used values order orderPos items (base + index * 8) value bits
  rcases separate with before | after
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

#print axioms HashTableReady32.after_array_word
end InitECandidate.Runtime
