import Guest.PancakeCryptoRefinement

/-!
# The two steps the first module left open

`cios_low_word_cancel` shows the CIOS reduction clears the low 64 bits of an
arbitrary accumulator, not only one below `2^64`. `binStep` shows the binary
Euclid loop of `modinv_bin` keeps `x * a = u + k * m` across a halving and
across a subtraction.
-/

namespace PancakeClose

open PancakeCrypto

theorem mul_mod_mul_right (u v n : Nat) : (u % n) * v % n = u * v % n :=
  Nat.mod_mul_mod u v n

theorem mul_mod_mul_left (u v n : Nat) : u * (v % n) % n = u * v % n := by
  rw [Nat.mul_comm u (v % n), Nat.mod_mul_mod, Nat.mul_comm]

/-- `p * inv ≡ -1 (mod 2^64)`, so `A + (A*inv mod 2^64)*p` is a multiple of
`2^64` for every `A`. -/
theorem cios_low_word_cancel (A : Nat)
    (hp : (blsMontInv * blsP) % 2 ^ 64 = 2 ^ 64 - 1) :
    (A + (A * blsMontInv % 2 ^ 64) * blsP) % 2 ^ 64 = 0 := by
  have h1 : (A * blsMontInv % 2 ^ 64) * blsP % 2 ^ 64 =
      A * blsMontInv * blsP % 2 ^ 64 := by rw [mul_mod_mul_right, Nat.mul_assoc]
  have h2 : A * blsMontInv * blsP % 2 ^ 64 = A * (blsMontInv * blsP) % 2 ^ 64 := by
    rw [← Nat.mul_assoc]
  have h3 : A * (blsMontInv * blsP) % 2 ^ 64 = A * (2 ^ 64 - 1) % 2 ^ 64 := by
    rw [← mul_mod_mul_left A (blsMontInv * blsP) (2 ^ 64), hp]
  have h4 : (A + A * (2 ^ 64 - 1)) % 2 ^ 64 =
      (A % 2 ^ 64 + A * (2 ^ 64 - 1) % 2 ^ 64) % 2 ^ 64 :=
    Nat.add_mod A (A * (2 ^ 64 - 1)) (2 ^ 64)
  have h5 : A * 1 + A * (2 ^ 64 - 1) = A * (1 + (2 ^ 64 - 1)) := by
    rw [Nat.mul_add]
  have h6 : 1 + (2 ^ 64 - 1) = 2 ^ 64 := by decide
  calc (A + (A * blsMontInv % 2 ^ 64) * blsP) % 2 ^ 64
      = (A % 2 ^ 64 + (A * blsMontInv % 2 ^ 64) * blsP % 2 ^ 64) % 2 ^ 64 := by
        rw [Nat.add_mod]
    _ = (A % 2 ^ 64 + A * (2 ^ 64 - 1) % 2 ^ 64) % 2 ^ 64 := by rw [h1, h2, h3]
    _ = (A + A * (2 ^ 64 - 1)) % 2 ^ 64 := by rw [← h4]
    _ = (A * 1 + A * (2 ^ 64 - 1)) % 2 ^ 64 := by rw [Nat.mul_one]
    _ = A * 2 ^ 64 % 2 ^ 64 := by rw [h5, h6]
    _ = 0 := Nat.mul_mod_left A (2 ^ 64)

/-- The concrete instance: `bls_mont_inv_spec` supplies `hp`. -/
theorem cios_low_word_forall (z : Nat) :
    (z + (z * blsMontInv % 2 ^ 64) * blsP) % 2 ^ 64 = 0 :=
  cios_low_word_cancel z bls_mont_inv_spec

/-- Even step of `modinv_bin`: both `u` and `x` are even, `m` odd, so the
witness halves too. -/
theorem binStep_even (u x a k m : Nat) (hu : u = 2 * (u / 2)) (hx : x = 2 * (x / 2))
    (hk : k = 2 * (k / 2)) (h : x * a = u + k * m) :
    (x / 2) * a = u / 2 + (k / 2) * m := by
  have h1 : 2 * ((x / 2) * a) = 2 * (u / 2 + (k / 2) * m) := by
    rw [← Nat.mul_assoc, ← hx, h, Nat.mul_add, ← Nat.mul_assoc, ← hk, ← hu]
  exact Nat.mul_left_cancel (by decide : 0 < 2) h1

theorem binStep_odd (u x a k m : Nat)
    (hx : x + m = 2 * ((x + m) / 2)) (h : x * a = u + k * m) :
    2 * (((x + m) / 2) * a) = u + a * m + k * m := by
  rw [← Nat.mul_assoc, ← hx, Nat.add_mul, h, Nat.add_assoc, Nat.add_comm (k * m),
    ← Nat.add_assoc, Nat.mul_comm m a]

theorem binStep_sub (u v x1 x2 a k1 k2 m : Nat)
    (h1 : x1 * a = u + k1 * m) (h2 : x2 * a = v + k2 * m) :
    x1 * a + v + k2 * m = x2 * a + u + k1 * m := by
  rw [h1, h2]
  omega

end PancakeClose
