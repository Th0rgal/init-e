import InitECandidate.Runtime.HashTableReadySetCallSupported
namespace InitECandidate.Runtime
open Flapjack

def hashSetRegistryCost (capacity keyLength items : BitVec 64) : Nat :=
  3 * capacity.toNat + 2 * (capacity * 2).toNat + keyLength.toNat + 13 +
    items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4)

/-- The supported-width set-call expression has a uniform finite ceiling
under the actual table-memory bound, independently of hash collisions. -/
theorem hashSetRegistryCost_le_ceiling (capacity keyLength items : BitVec 64)
    (capacityBound : capacity.toNat ≤ 33806089496)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (itemsBound : items.toNat ≤ capacity.toNat) :
    hashSetRegistryCost capacity keyLength items ≤ 2 ^ 72 := by
  have width : keyLength.toNat ≤ 52 := by
    rcases supported with rfl | rfl | rfl <;> decide
  have doubled : (capacity * (2 : BitVec 64)).toNat = capacity.toNat * 2 := by
    rw [BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)]
    rfl
  have product : items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ≤
      33806089496 * (67612178992 + 52 + 4) :=
    Nat.mul_le_mul (by omega) (by rw [doubled]; omega)
  unfold hashSetRegistryCost
  rw [doubled] at product ⊢
  omega

#print axioms hashSetRegistryCost_le_ceiling
end InitECandidate.Runtime
