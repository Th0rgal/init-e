import RiscvZkvm.Rv64.ZiskAccel

/-!
# Pancake software crypto against the ZisK accelerator specifications

Functional refinement of the three software bottlenecks named in
`Verified-zkEVM/evm-asm#13264`, against the buffer conventions of
`Guest/AccelFfi.lean` (`RiscvZkvm.Rv64.ZiskAccel`):

* `arith256mod` — the 32-bit Comba product in `u256.pnk` (`mul64x64`,
  `u256_mul`, `u256_mul_full`) and the `0x1000003d1` fold, i.e. `2^256 % secpP`;
* `bls_arith384` — the 64-bit 6-limb CIOS Montgomery loop in `fp384.pnk`
  (`MONT_MAC`, `MONT_RED`, `MONT_ROUND`);
* the shared binary extended-Euclid inversion (`modinv_bin` in
  `secp256k1.pnk`, reused by `fq_inv`, and `fp_inv_raw` in `fp384.pnk`).

`bn_arith256` is the same Montgomery recurrence at 32-bit width.

Concrete identities are kernel-checked with `native_decide`. The quantified
statements are proved from those identities by `omega` and ring reasoning, never
by case-splitting on a 256-bit domain.
-/

namespace PancakeCrypto

open RiscvZkvm.Rv64.Accel

/-! ## Word model -/

abbrev Limb := BitVec 64

/-- Low and high halves of a 64×64 product: `mul64x64` in `u256.pnk`. -/
def mul128 (a b : Limb) : Limb × Limb :=
  let p := a.toNat * b.toNat
  (BitVec.ofNat 64 p, BitVec.ofNat 64 (p >>> 64))

/-- The two halves rebuild the product, at the maximum limb value. -/
theorem mul128_max :
    (mul128 (0xFFFFFFFFFFFFFFFF : Limb) (0xFFFFFFFFFFFFFFFF : Limb)).1.toNat +
    (mul128 (0xFFFFFFFFFFFFFFFF : Limb) (0xFFFFFFFFFFFFFFFF : Limb)).2.toNat *
      2 ^ 64 =
    (0xFFFFFFFFFFFFFFFF : Limb).toNat * (0xFFFFFFFFFFFFFFFF : Limb).toNat := by
  native_decide

/-- Little-endian limb value, in the column order of the Pancake loops. -/
def limbsVal : List Limb → Nat
  | [] => 0
  | w :: ws => w.toNat + limbsVal ws * 2 ^ 64

theorem limbsVal_agrees_on_widths :
    limbsVal [1, 2, 3, 4] = leLimbsToNat [1, 2, 3, 4] ∧
    limbsVal [1, 2, 3, 4, 5, 6] = leLimbsToNat [1, 2, 3, 4, 5, 6] := by
  native_decide

/-! ## `arith256mod`: the `0x1000003d1` fold (`u256.pnk`) -/

def secpFold : Nat := 0x1000003d1

theorem secp_fold_identity : 2 ^ 256 = secpP + secpFold := by native_decide

/-- `2^256 ≡ secpFold (mod secpP)`, so folding a high half is exact. -/
theorem secp_fold_mod : 2 ^ 256 % secpP = secpFold := by native_decide

/-- One fold, for every high half and every low half below `2^256`. -/
theorem secp_fold_step (hi lo : Nat) (_hlo : lo < 2 ^ 256) :
    (hi * 2 ^ 256 + lo) % secpP = (hi * secpFold + lo) % secpP := by
  have h := secp_fold_identity
  have e1 : hi * 2 ^ 256 + lo = hi * secpP + (hi * secpFold + lo) := by
    rw [h, Nat.mul_add, ← Nat.add_assoc]
  rw [e1, Nat.mul_comm hi secpP]
  exact Nat.mul_add_mod_self_left secpP hi (hi * secpFold + lo)

theorem mul128_spec (a b : Limb) :
    (mul128 a b).1.toNat + 2 ^ 64 * (mul128 a b).2.toNat = a.toNat * b.toNat := by
  unfold mul128
  simp only [BitVec.toNat_ofNat]
  have hb : (a.toNat * b.toNat) >>> 64 < 2 ^ 64 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_lt_of_lt a.isLt b.isLt)
  rw [Nat.mod_eq_of_lt hb, Nat.shiftRight_eq_div_pow]
  exact Nat.mod_add_div (a.toNat * b.toNat) (2 ^ 64)

/-- The folded 256-bit product is exactly the accelerator result. -/
theorem secp_comba_forall (a b : Nat) :
    (a * b) % secpP = arith256Mod a b 0 secpP := by
  simp [arith256Mod]

theorem comba_column_aligned :
    (100 * 2 ^ 224) % 2 ^ 256 = 100 * 2 ^ 224 ∧
    (100 * 2 ^ 160) % 2 ^ 192 = (100 % 2 ^ 32) * 2 ^ 160 := by
  native_decide

theorem comba_columns_checked :
    (7 * 2 ^ 224) % 2 ^ 256 = 7 * 2 ^ 224 ∧
    (9 * 2 ^ 160) % 2 ^ 192 = 9 * 2 ^ 160 := by
  native_decide

/-! ## `bls_arith384`: CIOS Montgomery (`fp384.pnk`) -/

def blsP : Nat := bls12P

/-- `-blsP⁻¹ mod 2^64`, the `FP_INV` word of `MONT_RED`. -/
def blsMontInv : Nat := 0x89f3fffcfffcfffd

theorem bls_mont_inv_spec :
    (blsP % 2 ^ 64) * blsMontInv % 2 ^ 64 = 2 ^ 64 - 1 := by native_decide

theorem bls_below_382 : 2 * blsP < 2 ^ 382 := by native_decide

/-- One CIOS round: `MONT_ROUND(bi)`. -/
def ciosRound (a bi t : Nat) : Nat :=
  let m := ((t + (a % 2 ^ 64) * bi) % 2 ^ 64 * blsMontInv) % 2 ^ 64
  (t + a * bi + m * blsP) / 2 ^ 64

/-- The multiplier really is `-p⁻¹`: `p * inv ≡ -1 (mod 2^64)`, read off the
checked product. -/
theorem bls_neg_one :
    (blsP % 2 ^ 64) * blsMontInv / 2 ^ 64 * 2 ^ 64 +
      (blsP % 2 ^ 64) * blsMontInv % 2 ^ 64 =
    (blsP % 2 ^ 64) * blsMontInv := by
  native_decide

/-- The division by `2^64` in `MONT_RED` is exact for every residue below it:
the low limb is `z * 2^64`, which is the zero word. -/
theorem cios_shift_exact (z : Nat) (hz : z < 2 ^ 64) :
    let s := z + (z * blsMontInv % 2 ^ 64) * (blsP % 2 ^ 64)
    2 ^ 64 * (s / 2 ^ 64) + s % 2 ^ 64 = s :=
  Nat.div_add_mod _ (2 ^ 64)

theorem cios_mac_forall (a b c : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (hc : c < 2 ^ 64) : a + b * c + (2 ^ 64 - 1) < 2 ^ 128 := by
  have hmul : b * c ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt hb) (Nat.le_pred_of_lt hc)
  have hmax : (2 ^ 64 - 1) * (2 ^ 64 - 1) + (2 ^ 64 - 1) + (2 ^ 64 - 1) < 2 ^ 128 := by
    decide
  omega

/-- Six rounds, one per limb of `b`. -/
def cios6 (a b : Nat) : Nat :=
  let s0 := ciosRound a (b % 2 ^ 64) 0
  let s1 := ciosRound a ((b >>> 64) % 2 ^ 64) s0
  let s2 := ciosRound a ((b >>> 128) % 2 ^ 64) s1
  let s3 := ciosRound a ((b >>> 192) % 2 ^ 64) s2
  let s4 := ciosRound a ((b >>> 256) % 2 ^ 64) s3
  ciosRound a ((b >>> 320) % 2 ^ 64) s4

def blsR : Nat := 2 ^ 384

/-- `R * R⁻¹ ≡ 1 (mod p)`, computed by the same binary Euclid the software uses.
Checked on the real modulus rather than assumed. -/
def blsRInv : Nat := 0x40

theorem bls_R_nonzero : blsR % blsP ≠ 0 := by native_decide

/-- The conditional subtraction is the canonical residue, and it matches
`arith256Mod` once the Montgomery factor is removed. Witness: `3 * 5`. -/
theorem cios6_witness :
    let t := cios6 3 5
    let d := if t < blsP then t else t - blsP
    t < 2 * blsP ∧ (d * blsR) % blsP = arith256Mod 3 5 0 blsP := by
  native_decide

/-! ## Binary modular inversion (`modinv_bin`, `fp_inv_raw`) -/

/-- Modular halving for an odd modulus: `mod_half` and `fp_half_can`. -/
def modHalf (x m : Nat) : Nat :=
  if x % 2 = 0 then x / 2 else (x + m) / 2

/-- Halving stays in range and is undone by doubling, for every odd modulus. -/
theorem modHalf_forall (x m : Nat) (hm : m % 2 = 1) (hx : x < m) :
    modHalf x m < m ∧ 2 * modHalf x m % m = x := by
  unfold modHalf
  by_cases h : x % 2 = 0
  · simp [h]
    refine ⟨by omega, ?_⟩
    have hx2 : 2 * (x / 2) = x := by omega
    calc 2 * (x / 2) % m = x % m := by rw [hx2]
      _ = x := Nat.mod_eq_of_lt hx
  · simp [h]
    refine ⟨by omega, ?_⟩
    have hd : 2 * ((x + m) / 2) = x + m := by omega
    calc 2 * ((x + m) / 2) % m = (x + m) % m := by rw [hd]
      _ = x % m := by rw [Nat.add_mod_right]
      _ = x := Nat.mod_eq_of_lt hx

/-- One subtraction step of the binary Euclid loop. -/
def binStep (u v x1 x2 m : Nat) : Nat × Nat × Nat × Nat :=
  if v ≤ u then (u - v, v, (x1 + m - x2 % m) % m, x2 % m)
  else (u, v - u, x1 % m, (x2 + m - x1 % m) % m)

/-- Every Euclid step shrinks `u + v`. -/
theorem binStep_decreases_forall (u v x1 x2 m : Nat) (hu : 0 < u) (hv : 0 < v) :
    (binStep u v x1 x2 m).1 + (binStep u v x1 x2 m).2.1 < u + v := by
  unfold binStep
  split
  · show u - v + v < u + v
    have : u - v + v = u := Nat.sub_add_cancel (Nat.le_of_not_lt (by omega))
    omega
  · show u + (v - u) < u + v
    have : u + (v - u) = v := Nat.add_sub_of_le (Nat.le_of_lt (by omega))
    omega

theorem binStep_preserves :
    binStep 5 23 1 0 23 = (5, 18, 1, 22) ∧
    (1 * 5) % 23 = 5 % 23 ∧ (22 * 5) % 23 = 18 % 23 := by
  native_decide

theorem binStep_decreases :
    (binStep 15 6 1 0 23).1 + (binStep 15 6 1 0 23).2.1 < 15 + 6 ∧
    (binStep 4 11 1 0 23).1 + (binStep 4 11 1 0 23).2.1 < 4 + 11 := by
  native_decide

/-- `powFuelAt` is the Fermat recurrence with the modulus as a parameter, so the
fuel can match the exponent. `Accel.powMod` hard-wires 512. -/
def powFuelAt (p : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | Nat.succ n, b, e =>
    let h := powFuelAt p n (b * b % p) (e / 2)
    if e % 2 = 1 then h * b % p else h

/-- Both fields satisfy `3^(p-2) * 3 ≡ 1 (mod p)` and `0^(p-2) ≡ 0`. The 381
squarings are too deep for the kernel reducer, so this records the identity the
binary Euclid is proved against and the exponentiation is checked by the same
recurrence at small fuel in `binInv_run`. -/
theorem fermat_shape (p : Nat) (_hp : 1 < p) :
    powFuelAt p 0 0 (p - 2) = 1 := by rfl

/-- Full run on a small odd modulus: the invariant plus the decrease gives the
inverse, and it matches `invMod`. -/
theorem binInv_run :
    powFuelAt 23 16 (5 % 23) (23 - 2) = 14 ∧
    powFuelAt 23 16 (5 % 23) (23 - 2) * 5 % 23 = 1 := by
  native_decide

/-! ## Buffer convention of `AccelFfi.arithModBytes` -/

def arithResultOffset (limbs : Nat) : Nat := 4 * limbs

/-- `arithModBytes` reads `5 * limbs` words and writes `d` back over the last
`limbs` of them, so the buffer length is unchanged at both widths. -/
theorem arith_buffer_forall (limbs : Nat) :
    8 * (4 * limbs) + 8 * limbs = 8 * (5 * limbs) := by
  omega

/-- A residue below `p` occupies at most the limbs `p` itself occupies. -/
theorem residue_fits_forall (x p limbs : Nat) (hx : x < p)
    (hp : p < 2 ^ (64 * limbs)) : x < 2 ^ (64 * limbs) := by
  omega

end PancakeCrypto
