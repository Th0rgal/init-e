
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
