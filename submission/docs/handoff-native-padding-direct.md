# Handoff: native padding numeric bound (stopped at d9055903f)

## Green state

Branch `feat/fetched-native-padding`, head `d9055903f`
("feat(padding): direct kernel padding certificates for all 832 concrete sections").
Tree clean; builds exit 0 with zero `^submission.*error`.

`submission/InitECandidate/Runtime/NativePaddingDirect.lean` (green):

```lean
def padOk (b : Nat) : List (NativeLine 64) -> List (NativeLine 64) -> Bool
  | [], _ => true
  | _, [] => true
  | s :: ss, e :: es => decide ((lineBytes e).length <= (lineBytes s).length + b) && padOk b ss es

theorem PaddedNNN_padOk : padOk 4 FinalReencodeNNN.lines PaddedNNN.lines = true := by decide_cbv
```

832 such theorems, one per concrete section pair.  Axioms: `[propext]`.

## Numeric result

Every emitted instruction exceeds its source instruction's bytes by at most
`4` (one nop chunk).  The emission is 0 for 205012 of 205014 scanned segments;
the two exceptions are section 597 at offsets 20 and 3848 (recorded length 8
against encoding length 4).  So every binop/load/store/skip instance is in the
zero group.

## Other certified modules

- `Runtime/NativePaddingScan.lean`: `sourceSlackBound_four`,
  `pad_line_bytes_le`, `pad_line_labAsm_bytes_le`, `seg_padding_le_four`,
  `linesRel_forall2`, `label_not_mem_insts`, `padSlackOK`.
- `Runtime/NativePaddingChunks.lean`: 832 per-section span facts, 53+53 chunk
  compositions, 108 chain levels, `padded0_insts_slack`, `final0_insts_slack`.

## Open, with exact failure

Goal: `forall seg in padded0Certificate.segs, seg.paddingLen <= 4`
(composition of the per-section facts into `Final.padded0`).

Attempt: add `linesOf` (flatten of `secs.map (·.lines)`), `linesOf_append`,
`padOk_append` (needs a length side condition; positional pairing), per-chunk
`pair_len`/`pair_padOk` via `decide_cbv`, and 54 chain theorems over
`Final.finalN`/`Final.paddedN`.

Failures seen:

1. `decide_cbv` on a 16-section chunk blows up:
   `error: `simp` failed: maximum number of steps exceeded`
   (lines ~4306 etc. of the generated file).  Per-section `decide_cbv` is fine;
   2-section and 16-section chunks are not reliable.
2. `set_option maxSimpSteps ...` does not exist in Lean 4.33.1:
   `error: Unknown option `maxSimpSteps``.
3. Chain base case must be closed by `rfl`, not `simp [...]`: unfolding
   `Final.final53`/`Final.padded53` with `simp` also exceeds simp steps.
4. Ordering matters: `linesOf` must be defined before the per-chunk theorems,
   which must precede the chain theorems.

Next concrete step: avoid `decide_cbv` above one section.  Compose per section
with a Bool-valued `padOkN b a e = padOk b a e && (a.length == e.length)` plus a
`padOkN_append` lemma, then build each chunk by 16 nested append steps
referencing the per-section facts in the order given by the literal lists in
`def final` / `def padded`, and finally chain over `finalN`/`paddedN` as already
sketched.  Alternatively split chunk facts to two sections each (416 theorems)
and keep the same append structure.
