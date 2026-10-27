import Guest.PancakeCryptoRefinement

/-!
# Concrete Pancake steps

The bodies in `guest/src/lib/u256.pnk` and `guest/src/lib/secp256k1.pnk`, one
carry step at a time. `u256_add_carry` threads a carry through four
`__add_with_carry__` calls; `u256_sub` is `a + ~b + 1`; `modinv_bin` shifts a
limb right by one and pulls the low bit of the next limb in.
-/

namespace PancakeSteps

open PancakeCrypto

/-- One `__add_with_carry__` call: low word and carry out. -/
def addCarry (x y c : Nat) : Nat × Nat :=
  let s := x + y + c
  (s % 2 ^ 64, s / 2 ^ 64)

/-- The four-limb addition of `u256_add_carry`, carry in 0. -/
def u256Add (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) : Nat × Nat × Nat × Nat × Nat :=
  let r0 := addCarry a0 b0 0
  let r1 := addCarry a1 b1 r0.2
  let r2 := addCarry a2 b2 r1.2
  let r3 := addCarry a3 b3 r2.2
  (r0.1, r1.1, r2.1, r3.1, r3.2)

/-- A carry is 0 or 1 whenever every input limb fits in 64 bits. -/
def carry (x y c : Nat) : Nat := (x + y + c) / 2 ^ 64

theorem addCarry_bounded (x y c : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64)
    (hc : c ≤ 1) : carry x y c ≤ 1 := by
  unfold carry
  have : x + y + c < 2 * 2 ^ 64 := by omega
  omega

def word (x y c : Nat) : Nat := (x + y + c) % 2 ^ 64

theorem u256Add_low (a0 a1 b0 b1 : Nat)
    (ha0 : a0 < 2 ^ 64) (ha1 : a1 < 2 ^ 64) (hb0 : b0 < 2 ^ 64) (hb1 : b1 < 2 ^ 64) :
    word a0 b0 0 + word a1 b1 (carry a0 b0 0) * 2 ^ 64 +
      carry a1 b1 (carry a0 b0 0) * 2 ^ 128 =
    a0 + b0 + (a1 + b1) * 2 ^ 64 := by
  unfold word carry
  have e0 := Nat.mod_add_div (a0 + b0) (2 ^ 64)
  have e1 := Nat.mod_add_div (a1 + b1 + (a0 + b0) / 2 ^ 64) (2 ^ 64)
  omega

theorem u256Add_high (a2 a3 b2 b3 cin : Nat) (hc : cin ≤ 1)
    (ha2 : a2 < 2 ^ 64) (ha3 : a3 < 2 ^ 64) (hb2 : b2 < 2 ^ 64) (hb3 : b3 < 2 ^ 64) :
    word a2 b2 cin + word a3 b3 (carry a2 b2 cin) * 2 ^ 64 +
      carry a3 b3 (carry a2 b2 cin) * 2 ^ 128 =
    a2 + b2 + cin + (a3 + b3) * 2 ^ 64 := by
  unfold word carry
  have e2 := Nat.mod_add_div (a2 + b2 + cin) (2 ^ 64)
  have e3 := Nat.mod_add_div (a3 + b3 + (a2 + b2 + cin) / 2 ^ 64) (2 ^ 64)
  omega

/-- `u256_sub`: `a + ~b + 1`, and `~b = 2^64 - 1 - b` on a 64-bit limb. -/
def u256Sub (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) : Nat × Nat × Nat × Nat :=
  let r0 := addCarry a0 (2 ^ 64 - 1 - b0) 1
  let r1 := addCarry a1 (2 ^ 64 - 1 - b1) r0.2
  let r2 := addCarry a2 (2 ^ 64 - 1 - b2) r1.2
  let r3 := addCarry a3 (2 ^ 64 - 1 - b3) r2.2
  (r0.1, r1.1, r2.1, r3.1)

/-- `~b + 1 = 2^64 - b` on one limb, so four limbs give `a - b + 2^256` before
the final truncation. -/
theorem sub_complement (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    a + (2 ^ 64 - 1 - b) + 1 = a + 2 ^ 64 - b := by omega

theorem u256Sub_one_limb (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    word a (2 ^ 64 - 1 - b) 1 + carry a (2 ^ 64 - 1 - b) 1 * 2 ^ 64 =
      a + 2 ^ 64 - b := by
  unfold word carry
  have e := Nat.mod_add_div (a + (2 ^ 64 - 1 - b) + 1) (2 ^ 64)
  have hc := sub_complement a b ha hb
  omega

/-- One right shift of `modinv_bin`: limb `i` takes its high bit from limb
`i + 1`. `⟨(u.0 >>> 1) | (u.1 << 63), ...⟩` in `secp256k1.pnk`. -/
def shiftDown (lo hi : Nat) : Nat := lo / 2 + (hi % 2) * 2 ^ 63

theorem shiftDown_spec (lo hi : Nat) (hlo : lo < 2 ^ 64) (hhi : hi < 2 ^ 64) :
    shiftDown lo hi = (lo + hi * 2 ^ 64) / 2 % 2 ^ 64 := by
  unfold shiftDown
  omega

/-- Four limbs shifted down one bit equal the 256-bit value divided by two,
modulo `2^256`. -/
theorem shiftDown4_spec (w0 w1 w2 w3 : Nat)
    (h0 : w0 < 2 ^ 64) (h1 : w1 < 2 ^ 64) (h2 : w2 < 2 ^ 64) (h3 : w3 < 2 ^ 64) :
    shiftDown w0 w1 + shiftDown w1 w2 * 2 ^ 64 + shiftDown w2 w3 * 2 ^ 128 +
      (w3 / 2) * 2 ^ 192 =
    (w0 + w1 * 2 ^ 64 + w2 * 2 ^ 128 + w3 * 2 ^ 192) / 2 := by
  unfold shiftDown
  have d0 : w0 / 2 * 2 + w0 % 2 = w0 := by omega
  have d1 : w1 / 2 * 2 + w1 % 2 = w1 := by omega
  have d2 : w2 / 2 * 2 + w2 % 2 = w2 := by omega
  have d3 : w3 / 2 * 2 + w3 % 2 = w3 := by omega
  omega

/-- A limb lives at word `i`, hence at byte `8 * i`, in every accelerator
buffer. -/
theorem limb_byte_offset (i : Nat) : 8 * i + 8 = 8 * (i + 1) := by omega

end PancakeSteps
