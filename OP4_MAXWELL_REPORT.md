# Op 4 (Challenge B): Pancake crypto against the ZisK accelerator specs

Module: `Guest/PancakeCryptoRefinement.lean`, in the `op3-init-e-finite-k`
worktree (Lean 4.33.1, `RiscvZkvm.Rv64.ZiskAccel` already built). It refines the
three software bottlenecks named in `Verified-zkEVM/evm-asm#13264` against the
buffer conventions of `Guest/AccelFfi.lean`.

## What is proved, and for which inputs

Universally quantified, no `sorryAx`:

- `secp_fold_step` — for every `hi` and every `lo < 2^256`,
  `(hi * 2^256 + lo) % secpP = (hi * secpFold + lo) % secpP`, from the
  kernel-checked `secp_fold_identity : 2^256 = secpP + 0x1000003d1`. This is the
  single fold the secp256k1 software multiplier applies to a 512-bit product.
- `mul128_spec` — for every pair of 64-bit limbs, the two halves `mul64x64`
  returns rebuild the full product.
- `secp_comba_forall` — `(a * b) % secpP = arith256Mod a b 0 secpP` for every
  `a, b`. That is the `arith256mod` accelerator with a zero addend.
- `cios_mac_forall` — a `MONT_MAC` sum of three limbs stays below `2^128`.
- `cios_shift_exact` — dividing by `2^64` in `MONT_RED` drops only the low limb,
  for every residue below `2^64`.
- `modHalf_forall` — for every odd modulus and every `x < m`, halving stays in
  range and doubling recovers `x`. This is `mod_half` and `fp_half_can`.
- `binStep_decreases_forall` — every binary-Euclid step strictly shrinks `u + v`.
- `arith_buffer_forall`, `residue_fits_forall` — the `a, b, c, m, d` block of
  `AccelFfi.arithModBytes` is exactly `5 * limbs` words, and a residue below `p`
  fits in the limbs `p` occupies.

Closed witnesses, kernel-checked with `native_decide`: `secp_fold_identity`,
`bls_mont_inv_spec` (`-blsP^-1 mod 2^64 = 0x89f3fffcfffcfffd`), `bls_below_382`
(`2p < 2^382`), `cios6_witness` (the six-round CIOS product of 3 and 5 matches
`arith256Mod`), `binInv_run` (`5^(23-2) ≡ 14`, and `14 * 5 ≡ 1`).

## Audit

`turbo-lean --json audit-spec Guest/PancakeCryptoRefinement.lean`:

- `ok: true`, `total_specs_audited: 24`, `tight_specs: 24`
- `vacuous_specs: 0`, `trivial_specs: 0`

`#print axioms` on the nine quantified theorems: no `sorryAx`. The only axioms
are `propext`, `Quot.sound` and, for `mul128_spec`, `Classical.choice`.

## Not proved

- `cios_low_word_forall` for an arbitrary `z`, i.e. that the low limb of
  `z + m*p` is zero for every `z` rather than every `z < 2^64`. The congruence
  `p * inv ≡ -1 (mod 2^64)` is checked (`bls_mont_inv_spec`); lifting it through
  `Nat.add_mod` / `Nat.mul_mod` did not go through in this toolchain.
- `binStep_preserves_forall`. The loop invariant `x1*a ≡ u (mod m)` is stated and
  checked on a witness (`binStep_preserves`), but the general step needs a
  modular-arithmetic lemma this toolchain's `omega` does not apply.
- `powFuelAt` agrees with `Accel.powMod` only in shape. `Accel.powMod` hard-wires
  512 iterations, which the kernel reducer cannot run on a 381-bit exponent, so
  the Fermat check is stated at fuel 0 and the real exponentiation is checked at
  fuel 16 on a 5-bit modulus.

## Sources read

`guest/src/lib/u256.pnk` (`mul64x64`, `u256_mul`, `u256_mul_full`),
`guest/src/lib/fp384.pnk` (`MONT_MAC`, `MONT_RED`, `MONT_ROUND`, `fp_inv_raw`),
`guest/src/lib/secp256k1.pnk` (`modinv_bin`, `mod_half`), `Guest/AccelFfi.lean`
(`arithModBytes`), and `RiscvZkvm/Rv64/ZiskAccel.lean` (`arith256Mod`, `secpP`,
`bls12P`, `invMod`).
