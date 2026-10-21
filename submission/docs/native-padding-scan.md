# Native padding: opcode-associated scan, certificate, and checked transfer

Module: `submission/InitECandidate/Runtime/NativePaddingScan.lean`
(namespace `InitECandidate.Runtime.NativePadding`).

This document records (1) what already existed in the repository, with
`file:line` for every fact, (2) what did not exist and therefore had to be
built, and (3) the resulting objects and theorems, including the axiom report
and a computed run of the scanner on the real artifact.

## 1. Recon: what exists

### 1.1 Instruction fetch (the real `fetch` machinery)

* `asmFetchAux` — `Flapjack/Compiler/Backend/LabSem/Navigation.lean:21`
  (`def asmFetchAux (position : Nat) (code) : Option (Line …)`), the LabLang
  counter-machine fetch that walks sections, skips labels and counts
  instructions. Well-founded on the code argument.
* `asmFetch` — `Flapjack/Compiler/Backend/LabSem/Navigation.lean:36`.
* `asmCodeLength` — `Flapjack/Compiler/Backend/LabSem/Navigation.lean:41`.
* `asmFetchImp` — `Flapjack/Compiler/Backend/LabSem/Navigation.lean:133`.
* `isLabelHOL` — `Flapjack/Compiler/Backend/LabSem/Classifier.lean:12`
  (labels carry no instruction).

There is **no** existing lemma that presents `asmFetchAux` as a list index over
the emitted instruction stream; the counter-machine formulation (a numeric
position that skips labels) is what all downstream proofs use.

### 1.2 Code similarity (the real `codeSimilar` machinery)

* `lineSimilar` — `Flapjack/Compiler/Backend/LabToTarget/CodeSimilar.lean:18`.
* `codeSimilar` — `Flapjack/Compiler/Backend/LabToTarget/CodeSimilar.lean:34`
  (section-wise `LinesRel lineSimilar`).
* `codeSimilar_refl` — `…/CodeSimilar.lean:64`.

The bridge from `codeSimilar` to a fetch already existed:

* `codeSimilar_asmFetchAux` —
  `Flapjack/Compiler/Backend/LabToTarget/Navigation.lean:12`:
  `codeSimilar c1 c2 → Option.Rel lineSimilar (asmFetchAux pc c1) (asmFetchAux pc c2)`.

This is the bridge that the transfer below **reuses** (it is named in the proof
and needed no new fetch/similarity theory).

### 1.3 Padding

* `padBytes` — `Flapjack/Compiler/Backend/LabToTarget/Padding.lean:44`
  (extend a payload to its recorded length with the nop chunk).
* `addNop` — `…/Padding.lean:54` (append one nop chunk to the last emitted
  instruction of the accumulator).
* `padSection` — `…/Padding.lean:71` (`REVERSE aux` accumulator style, exactly
  HOL `lab_to_target$pad_section`).
* `padCode` — `…/Padding.lean:92`.
* Similarity of padding: `lineSimilar_addNop`
  (`…/CodeSimilar/Padding.lean:57`), `lineSimilar_padSection`
  (`…/CodeSimilar/Padding.lean:80`), `codeSimilar_padCode`
  (`…/CodeSimilar/Padding.lean:92`).

### 1.4 Bytes

* `lineBytes` — `Flapjack/Compiler/Backend/LabToTarget/RemoveLabels.lean:159`
  (the bytes a line contributes; `[]` for labels).
* `progToBytes` — `…/RemoveLabels.lean:171`.

### 1.5 The artifact

* `Final.final0` — `submission/InitECandidate/Proofs/BackendStages/Final.lean:590`
  (the pre-padding final code).
* `Final.padded0` — `…/Final.lean:591` (`FinalChunkStubs.padded ++ padded1`).
* `Final.padding0_eq` — `…/Final.lean:594`:
  `LabToTarget.padCode (riscvConfig.encode (.inst .skip)) final0 = padded0`.
* `Final.valid0` — `…/Final.lean:597`.
* `Final.padded0` *is* the code whose bytes are the ROM image:
  `suffix0_eq` (`…/BackendStages/Bytes.lean:218`,
  `LabToTarget.progToBytes Final.padded0 = ByteData.chunks0`) and
  `compile_eq` (`…/Bytes.lean:221`).
* Concrete sections: `Padded597_eq`
  (`…/BackendStages/Padded597.lean:14817`,
  `padSection nop FinalReencode597.lines [] = Padded597.lines`) — one of the
  sections where `padCode` genuinely pads.

Precedent for computable scans over the artifact:
`submission/InitECandidate/Runtime/LabPositionGapScan.lean:9` (`gapScan`) and
`:15` (`flatPosition`).

## 2. What did not exist and had to be built

1. **A per-opcode padding record.** `padCode` is a rewrite of lines, and its
   result only survives as a flat byte list (`progToBytes`). Given only
   `Final.padded0`'s bytes, the per-instruction split of trailing nop bytes is
   *not* recoverable: `padBytes` pads up to a recorded `len` that is erased by
   `padCode`'s output, and `addNop` inserts nops that belong to a *previous*
   instruction but sit between two decoded instructions. Hence the scanner is
   defined as a **lock-step walk of the source instruction stream against the
   emitted instruction stream**, not as a decode of padded bytes alone.
2. **Instruction indexing lemmas for the fetch** (`NativePaddingScan.lean:58`,
   `:228`–`:260`): `asmFetchAux pc code = (insts code)[pc]?` and the fact that
   padding preserves the instruction index (`insts_padCode_length`,
   `scanInsts_padCode`).
3. **A padding-accounting relation** (`PadKeeps`, `PadsRel`,
   `NativePaddingScan.lean:262`–`:430`): each source line's bytes are a
   prefix of the emitted line's bytes, positionally, through
   `padBytes`/`addNop`/`padSection`/`padCode`. This is the concrete,
   *byte-arithmetic* content (no length premise is assumed anywhere).
4. **The offset chain** (`OffsetChain`, `NativePaddingScan.lean:432`–`:466`):
   recorded offsets are contiguous from `base`, and every instruction lies
   inside the padded image.
5. **The certificate and the transfer** (below).

## 3. The scanner (computable, no `Classical.choose`, no `noncomputable`)

```
structure PadSeg (width : Nat) [NeZero width] where
  sectionId : Nat                 -- section the instruction belongs to
  source    : NativeLine width    -- unpadded line (opcode payload)
  emitted   : NativeLine width    -- line actually emitted by padCode
  offset    : Nat                 -- byte offset of its first payload byte
```

with total accessors `payload = lineBytes emitted`, `opcode = lineBytes source`,
`padding = payload.drop opcode.length`, `size = payload.length`,
`paddingLen = padding.length` (all `abbrev`, so they compute).

```
def scanInsts (base) : List (Nat × NativeLine) → List NativeLine → List (PadSeg)
  | [], _ => []
  | _ :: _, [] => []
  | (sid, line) :: lines, emit :: emits =>
      ⟨sid, line, emit, base⟩ :: scanInsts (base + (lineBytes emit).length) lines emits

def scanCode base source padded :=
  scanInsts base (codeInsts source) (insts padded)
```

`insts` is the emitted instruction stream `code.filter notLabel` flattened over
sections — the same list `asmFetchAux` counts through
(`asmFetchAux_eq_insts`). `codeInsts` is the same stream of the *unpadded*
code, tagged with section ids.

Proven about the scanner (all `#print axioms` ⊆
`{propext, Classical.choice, Quot.sound}`):

* `scanInsts_maps` (`:186`): the scanner's `source` map is the source stream and
  its `emitted` map is the emitted stream.
* `scanInsts_padCode` (`:245`): for `padded = padCode nop source` the scanner
  returns one segment per instruction of the padded code, and the two maps
  agree with `insts source` / `insts padded`. This is what makes the
  instruction index of a segment equal to the logical `pc`.
* `offsetChain_scanInsts` (`:438`): the offsets the scanner records form an
  `OffsetChain base` over its own output (no axioms at all).
* `offsetChain_bound` (`:452`): every recorded instruction fits inside the
  padded image.
* `padCode_padsRel` (`:418`) / `padSection_keeps` (`:411`) /
  `padsRel_getElem?` (`:321`): the `pc`-th source instruction's bytes are a
  prefix of the `pc`-th emitted instruction's bytes — *concrete arithmetic*,
  derived from `padBytes_prefix` (`:338`) and `addNop_padsRel` (`:348`), never
  assumed.

## 4. The certificate, produced by the scanner

```
structure PadCertificate (width : Nat) [NeZero width] where
  nop     : List (BitVec 8)                    -- the nop chunk padCode repeats
  base    : Nat                                -- scan start offset
  source  : List NativeCode                    -- unpadded code
  padded  : List NativeCode                    -- the emitted, padded code
  segs    : List (PadSeg width)                -- ≔ scanCode base source padded
  padded_eq     : padCode nop source = padded
  scanned       : segs = scanCode base source padded       -- rfl
  complete      : segs.length = (insts padded).length
  chain         : OffsetChain base segs
  sources_eq    : segs.map source  = insts source
  emitted_eq    : segs.map emitted = insts padded
  padding_accounted : PadsRel (insts source) (insts padded)
  opcode_stream : (segs.map opcode).flatten  = ((insts source).map lineBytes).flatten
  payload_stream: (segs.map payload).flatten = ((insts padded).map lineBytes).flatten
  lengths_agree : (segs.map size).sum        = ((insts padded).map lineBytes).flatten.length
```

`PadCertificate.ofScan nop base source padded (h : padCode nop source = padded)`
(`:506`) **builds the whole structure**: `segs` is literally
`scanCode base source padded` (`scanned := rfl`), and every other field is a
theorem about that computation. The only hypothesis is the code-level equation
`padCode nop source = padded`, which for the artifact is
`Final.padding0_eq` — a proved theorem, not an assumption about the scanner.

## 5. The transfer through the real `fetch` and `codeSimilar`

`PadCertificate.codeSimilar` (`:547`) *derives* `codeSimilar source padded` from
`codeSimilar_padCode` at the certificate's own data (nothing is assumed).

`padScan_fetch_transfer` (`:592`), conclusion `PaddedFetch cert pc line`:

```
asmFetchAux pc cert.source = some line →
  ∃ seg ∈ cert.segs, ∃ line',
    asmFetchAux pc cert.padded = some line'          -- the real fetch
  ∧ lineSimilar line line'                           -- the fetched instruction relates
  ∧ seg.source = line ∧ seg.emitted = line'
  ∧ (cert.segs.map offset)[pc]?  = some seg.offset   -- scanner-computed offset
  ∧ (cert.segs.map payload)[pc]? = some (lineBytes line')
  ∧ lineBytes line <+: lineBytes line'               -- padding is a byte suffix
  ∧ seg.offset + (lineBytes line').length ≤
      cert.base + ((insts cert.padded).map lineBytes).flatten.length
```

Proof: `codeSimilar_padCode` + `codeSimilar_refl` give the code similarity,
`codeSimilar_asmFetchAux` — the **existing** bridge, reused unchanged — turns
it into `Option.Rel lineSimilar (asmFetchAux pc source) (asmFetchAux pc padded)`,
`asmFetchAux_eq_insts` identifies the fetch with the instruction index, and the
scanner's own fields (`sources_eq`, `emitted_eq`, `padding_accounted`,
`chain`, `lengths_agree`) supply the segment, the offset, the payload and the
bound.

Remark on "codeSimilar for the fetched instruction": `codeSimilar` is a
whole-code relation (`Section`-wise `LinesRel lineSimilar`); its per-line
component *is* `lineSimilar`, which is exactly what the bridge concludes for the
fetched instruction. The code-level statement for the real pair is also
provided (`padded0_codeSimilar`) and is derived, not assumed.

### Instantiation at the artifact

```
def paddingNop : List (BitVec 8) := riscvConfig.encode (.inst .skip)      -- :642
def padded0Certificate : PadCertificate 64 :=
  PadCertificate.ofScan paddingNop 0 Final.final0 Final.padded0 Final.padding0_eq  -- :648
theorem padded0_fetch_transfer (pc) (line)
    (fetch : asmFetchAux pc Final.final0 = some line) : PaddedFetch padded0Certificate pc line  -- :652
theorem padded0_codeSimilar : codeSimilar Final.final0 Final.padded0                        -- :658
```

## 6. Axiom report (`#print axioms`, printed at the end of the module)

```
asmFetchAux_eq_insts            [propext, Quot.sound]
scanInsts_padCode               [propext, Classical.choice, Quot.sound]
padSection_keeps                [propext, Quot.sound]
padCode_padsRel                 [propext, Quot.sound]
offsetChain_scanInsts           (none)
offsetChain_bound               [propext, Quot.sound]
PadCertificate.ofScan           [propext, Classical.choice, Quot.sound]
PadCertificate.codeSimilar      [propext, Quot.sound]
PadCertificate.segment_keeps    [propext, Quot.sound]
padScan_fetch_transfer          [propext, Quot.sound]
padded0_fetch_transfer          [propext, Classical.choice, Quot.sound]
padded0_codeSimilar             [propext, Classical.choice, Quot.sound]
section597_pad                  [propext, Quot.sound]
section597_scan_segments        [propext]
section597_fetch_transfer       [propext, Classical.choice, Quot.sound]
```

No `sorry`, no new axiom, no circular hypothesis.

## 7. Computed evidence that the certificate is scanner output

The scanner is executable, so it can be run on the artifact's own sections.
Section 597 of the final code is one where `padCode` really pads (two
instructions with 4 opcode bytes and recorded length 8):

```
theorem section597_pad :
    LabToTarget.padCode paddingNop ([FinalReencode597] : List (NativeCode 64)) = [Padded597]  -- :662

theorem section597_scan_segments :                                                           -- :675
    ((scanCode 0 [FinalReencode597] [Padded597]).filter (fun s => !(s.paddingLen == 0))).map
        (fun s => (s.offset, s.opcode.length, s.payload.length))
      = [(20, 4, 8), (3848, 4, 8)]        := by decide_cbv
```

i.e. `decide_cbv` computes the scanner's output on concrete artifact code: at
byte offsets 20 and 3848 in the padded section, an instruction with 4 opcode
bytes is emitted with 8 bytes (4 bytes of native padding each), and the
corresponding `PadCertificate` (`section597Certificate`, `:683`) transfers
fetches on that section (`section597_fetch_transfer`, `:687`).

## 8. Reproducing the build

```
A=<build>/lib/lean; N=$(cat shared_lean_path.txt)
LEAN_PATH="$A:$N" lean --root=submission \
  submission/InitECandidate/Runtime/NativePaddingScan.lean
```
