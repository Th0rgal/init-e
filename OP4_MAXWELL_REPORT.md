# Op 4 — Pancake crypto against the ZisK accelerator specs

Branch `op4-pancake-crypto`, worktree
`/var/lib/sandboxed-node/campaigns/worktrees/op4-init-e-crypto`. Three modules,
42 theorems, all tight, none vacuous, none trivial, no `sorryAx`.

| Module | Specs | What it covers |
| --- | ---: | --- |
| `Guest/PancakeCryptoRefinement.lean` | 27 | secp256k1 Comba fold, `mul128`, Montgomery MAC bound, `modHalf`, buffer widths for BN254 and the hashes |
| `Guest/PancakeSteps.lean` | 8 | `u256_add` carry chain, `u256_sub` complement, `modinv_bin` one-bit shift, limb byte offset |
| `Guest/PancakeClose.lean` | 7 | CIOS low-word cancellation for every accumulator, and the three binary-Euclid steps |

`turbo-lean --json audit-spec` on each module: `ok: true`, `vacuous_specs: 0`,
`trivial_specs: 0`. `#print axioms` shows `propext`, `Quot.sound`, and
`Classical.choice` for `mul128_spec` only.

## The 18 accelerator entries

`Guest/AccelFfi.lean`, `acceleratorBytes`:

| FFI | Limbs | Pancake source |
| --- | ---: | --- |
| `keccakf` | 25 words | `guest/src/lib/keccak.pnk` |
| `sha256f` | 4 + 8 words | `guest/src/lib/sha256.pnk` |
| `arith256mod` | 4 | `guest/src/lib/u256.pnk` (`u256_mul`, Comba, fold by `0x1000003d1`) |
| `bn_arith256` | 4 | `guest/src/lib/bn254.pnk` (32-bit Montgomery) |
| `bls_arith384` | 6 | `guest/src/lib/fp384.pnk` (64-bit CIOS, `MONT_MAC` / `MONT_RED`) |
| `secpadd` | 4 | `guest/src/lib/secp256k1.pnk` |
| `secpdbl` | 4 | `guest/src/lib/secp256k1.pnk` |
| `bn_g1_add` | 4 | `guest/src/lib/bn254.pnk` |
| `bn_g1_dbl` | 4 | `guest/src/lib/bn254.pnk` |
| `bn_fp2_add` | 4 | `guest/src/lib/bn254.pnk` |
| `bn_fp2_sub` | 4 | `guest/src/lib/bn254.pnk` |
| `bn_fp2_mul` | 4 | `guest/src/lib/bn254.pnk` |
| `bls_g1_add` | 6 | `guest/src/lib/bls12381.pnk` |
| `bls_g1_dbl` | 6 | `guest/src/lib/bls12381.pnk` |
| `bls_fp2_add` | 6 | `guest/src/lib/bls12381.pnk` |
| `bls_fp2_sub` | 6 | `guest/src/lib/bls12381.pnk` |
| `bls_fp2_mul` | 6 | `guest/src/lib/bls12381.pnk` |
| `blake2bround` | 1 + 16 + 16 | `guest/src/lib/blake2.pnk` |

`bn_arith256` and `arith256mod` share `arithModBytes 4`. `bls_arith384` uses
`arithModBytes 6`. The curve and `fp2` entries go through `curveAddBytes`,
`curveDblBytes` and `complexBytes`.

## What is proved

- Comba: `(hi * 2^256 + lo) % secpP = (hi * secpFold + lo) % secpP` for every
  `lo < 2^256`, from `2^256 = secpP + secpFold`. `(a * b) % secpP` matches
  `arith256Mod`.
- CIOS: for every `A`, `A + (A * blsMontInv % 2^64) * blsP` is a multiple of
  `2^64`. The proof uses `Nat.mod_mul_mod` on two factors at a time, then
  `blsMontInv * blsP ≡ -1 (mod 2^64)`, then `Nat.mul_mod_left`.
- Carry: a 64-bit limb addition produces a carry of 0 or 1, and the low pair
  and the high pair each rebuild their 128-bit sum. `a + ~b + 1 = a - b + 2^64`
  on one limb.
- Binary Euclid: when `x` and `k` are even the witness halves; when `x + m` is
  even, `2 * ((x+m)/2) * a = u + a*m + k*m`; subtraction preserves
  `x1*a + v + k2*m = x2*a + u + k1*m`.
- Buffers: keccakf is 200 bytes, sha256f 96, blake2bround 264. A limb `i` sits
  at byte `8*i`.

## What is not proved

- `Accel.powMod` at its hard-wired 512 iterations on a 381-bit exponent. The
  kernel reducer does not finish it. The Fermat check is a closed witness at
  fuel 16 on a 5-bit modulus (`binInv_run`).
- The subtraction step of `modinv_bin` as a `Nat` subtraction `x1 - x2`. `omega`
  rejects an unbounded `Nat.sub`, so the theorem is stated as the additive
  equality above, which is what the loop invariant needs.
