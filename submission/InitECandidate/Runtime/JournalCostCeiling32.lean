import InitECandidate.Runtime.HashTableReady32
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A fixed finite ceiling for either original journal operation's call bound.
It follows from the live table's heap-bounded capacity, not a growth assumption. -/
theorem HashTableReady32.journal_cost_ceiling {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state) :
    5 * capacity.toNat + 2 * (capacity * 2).toNat + 83 + items.toNat * ((capacity * 2).toNat + 36) ≤ 2 ^ 72 ∧
      capacity.toNat * 39 + 41 ≤ 2 ^ 72 := by
  have cap := ready.live.arrays.capacity_bounded state table keys stride capacity used values order orderPos items bits
  have count := ready.live.arrays.room
  have doubled : (capacity * (2 : BitVec 64)).toNat = capacity.toNat * 2 :=
    BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)
  have product : items.toNat * ((capacity * 2).toNat + 36) ≤ 33806089496 * (33806089496 * 2 + 36) :=
    Nat.mul_le_mul (by omega) (by rw [doubled]; omega)
  rw [doubled] at product ⊢
  constructor <;> omega

#print axioms HashTableReady32.journal_cost_ceiling
end InitECandidate.Runtime
