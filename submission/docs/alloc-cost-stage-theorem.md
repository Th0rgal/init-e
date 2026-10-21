
## Numeric native-padding measurement over `Final.padded0` (evaluated, kernel proof open)

Evaluating the scanner on the artifact itself
(`(scanCode 0 Final.final0 Final.padded0)`):
  total scanned instruction segments           = 205014
  segments with paddingLen != 0                = 2
  max paddingLen                               = 4

The two nonzero cases are the already kernel-checked ones of section 597:
offsets 20 and 3848, opcode length 4, emitted length 8 (deficit 4).  So the
opcode-associated padding bound is 4 globally and 0 for 205012 of 205014
instructions - the "zero for binop / load / store / skip" case holds for all but
those two classes.  In the form requested (recordedLen vs encode length plus
4*bound): bound 0 is FALSE at exactly those two lines, bound 1 is true
everywhere.

CERTIFICATION STATUS.  A single `decide_cbv` over the whole code does NOT
terminate (killed after 30+ minutes: 205014 segments exceed the kernel's
reduction budget), so this bound is currently measured, not proved.  The route
to a kernel proof is chunking: per-section `decide_cbv` is cheap (section 597
proves in seconds), combined with a section-indexed fetch lemma, giving
"paddingLen <= 4 on section 597, = 0 elsewhere".  The general per-class
statement additionally needs `recordedLen line = (lineBytes line).length` for
binop/load/store/skip, which the pin does not supply (`padSection` consumes the
recorded `len` field directly, `Padding.lean:36-43,60-69`).

## Native padding: certified numeric bound (state at c613aa653)

Certified kernel facts on `feat/fetched-native-padding`:

- `sourceSlackBound_four` : every instruction of `Final.final0` has
  `lineSlack line <= 4`.
- `pad_line_bytes_le` / `pad_line_labAsm_bytes_le` : a line padded by
  `padSection` exceeds its source bytes by exactly the source line's slack.
- `seg_padding_le_four` : `source <+: emitted` and
  `emitted.length - source.length <= 4` give `seg.paddingLen <= 4`.
- `linesRel_forall2` : `LinesRel rel xs ys -> List.Forall2 rel xs ys`.
- `label_not_mem_insts` : labels never occur in `insts`.
- span bounds: `(insts Final.final0).all (padSlackOK 4)` and
  `(insts Final.padded0).all (padSlackOK 4)`, built from 832 per-section
  `decide_cbv` facts, 53+53 chunk compositions and 108 chain inductions.

Numeric result: padding is at most 4 bytes, i.e. one nop chunk, and it is 0 for
205012 of the 205014 scanned segments.  The two nonzero cases are section 597 at
offsets 20 and 3848 (recorded length 8 against encoding length 4).  So every
binop/load/store/skip instance is in the zero group.

Still unproved: `forall seg in padded0Certificate.segs, seg.paddingLen <= 4`.
It needs one list lemma bounding each emitted line's byte excess over its source
by 4, handling `padSection`'s label clause: a label with nonzero recorded length
applies `addNop` to the accumulated prefix, and `addNop` (Padding.lean:56-64) adds
exactly one 4-byte chunk to the first instruction it meets and does not recurse,
so the bound of 4 survives.  An append-shaped accumulator identity
`padSection nop lines aux = aux.reverse ++ images` was tried and refuted by that
label clause; the correct form is label-adjacency aware.
