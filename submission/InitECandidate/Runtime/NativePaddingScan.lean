import InitECandidate.Proofs.BackendStages.Final
import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.Padding
import Flapjack.Compiler.Backend.LabToTarget.Navigation
import Flapjack.Compiler.Backend.LabToTarget.RemoveLabels
import InitECandidate.Proofs.BackendStages.Padded597
import InitECandidate.Proofs.BackendStages.FinalReencode597

/-!
# Native padding scanner for the final emitted code

This file scans the *actual* padded final-assembly object
`InitECandidate.Proofs.BackendStages.Final.padded0` (defined at
`submission/InitECandidate/Proofs/BackendStages/Final.lean:591`) together with the
unpadded pre-padding object `Final.final0`, and records, for every emitted
instruction, its opcode bytes, the trailing native padding bytes added by
`padCode`, and its byte offset in the padded image.  The scan output is then
turned into a certificate whose fields are proven facts of that output, and the
certificate transports a source `asmFetchAux` fetch to the padded code.
-/

namespace InitECandidate.Runtime.NativePadding

open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- The native LabLang line carrier at a positive word width. -/
abbrev NativeLine (width : Nat) [NeZero width] :=
  Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
    (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)

/-- The native LabLang section carrier. -/
abbrev NativeCode (width : Nat) [NeZero width] := Section (NativeLine width)

/-- The fixpoint of `isLabelHOL`: labels carry no executable instruction. -/
abbrev notLabel {width : Nat} [NeZero width] (line : NativeLine width) : Bool := !isLabelHOL line

/-- The emitted instruction stream: the non-label lines of every section, in
emission order.  This is the list `asmFetchAux` counts through. -/
def insts {width : Nat} [NeZero width] (code : List (NativeCode width)) : List (NativeLine width) :=
  (code.map (fun sec => sec.lines.filter notLabel)).flatten

theorem insts_cons {width : Nat} [NeZero width] (sid : Nat) (lines : List (NativeLine width))
    (rest : List (NativeCode width)) :
    insts (⟨sid, lines⟩ :: rest) = lines.filter notLabel ++ insts rest := rfl

theorem insts_line_cons {width : Nat} [NeZero width] (sid : Nat) (line : NativeLine width)
    (lines : List (NativeLine width)) (rest : List (NativeCode width)) :
    insts (⟨sid, line :: lines⟩ :: rest) =
      (if isLabelHOL line then [] else [line]) ++ insts (⟨sid, lines⟩ :: rest) := by
  rw [insts_cons, insts_cons, List.filter_cons]
  cases h : isLabelHOL line <;> simp [notLabel, h]

/-- **Fetch is the instruction-stream lookup.** `asmFetchAux` skips labels and
empty sections, so the instruction it fetches at `pc` is exactly entry `pc` of
the non-label line stream. -/
theorem asmFetchAux_eq_insts {width : Nat} [NeZero width] (pc : Nat)
    (code : List (NativeCode width)) : asmFetchAux pc code = (insts code)[pc]? := by
  fun_induction asmFetchAux pc code with
  | case1 position =>
      simp only [insts, List.map_nil, List.flatten_nil]
      rfl
  | case2 position sectionId rest ih =>
      simpa only [insts_cons, List.filter_nil, List.nil_append] using ih
  | case3 position sectionId line lines rest hlab ih =>
      rw [ih, insts_line_cons, hlab]
      simp only [↓reduceIte, List.nil_append]
  | case4 sectionId line lines rest hlab =>
      have hfalse : isLabelHOL line = false := by
        cases hh : isLabelHOL line <;> simp_all
      rw [insts_line_cons, hfalse]
      simp only [Bool.false_eq_true, ↓reduceIte, List.singleton_append,
        List.getElem?_cons_zero]
  | case5 position sectionId line lines rest hlab hpos ih =>
      have hfalse : isLabelHOL line = false := by
        cases hh : isLabelHOL line <;> simp_all
      rw [ih, insts_line_cons, hfalse]
      simp only [Bool.false_eq_true, ↓reduceIte, List.singleton_append]
      have hpos' : position = (position - 1) + 1 := by omega
      rw [hpos', List.getElem?_cons_succ, Nat.add_sub_cancel]

/-- `lineSimilar` agrees on label-ness: the padded and unpadded line streams
have their labels at the same positions. -/
theorem lineSimilar_isLabelHOL {width : Nat} [NeZero width] {left right : NativeLine width}
    (rel : lineSimilar left right) : isLabelHOL left = isLabelHOL right := by
  cases left <;> cases right <;> simp_all [lineSimilar, isLabelHOL]

theorem linesRel_refl {width : Nat} [NeZero width] (lines : List (NativeLine width)) :
    LinesRel lineSimilar lines lines := by
  induction lines with
  | nil => exact .nil
  | cons line lines ih => exact .cons (lineSimilar_refl line) ih

/-! ## The scanner -/

/-- One emitted instruction of the padded code, associated with the opcode line
it came from: the source line before padding, the padded line that is actually
emitted, and the offset of its first payload byte in the padded image. -/
structure PadSeg (width : Nat) [NeZero width] where
  /-- Section the instruction belongs to. -/
  sectionId : Nat
  /-- The unpadded source line (opcode payload before padding). -/
  source : NativeLine width
  /-- The line actually emitted by `padCode`. -/
  emitted : NativeLine width
  /-- Index of the first payload byte of this instruction in the padded image. -/
  offset : Nat

/-- The bytes actually emitted for the instruction (its padded payload). -/
abbrev PadSeg.payload {width : Nat} [NeZero width] (seg : PadSeg width) : List (BitVec 8) :=
  lineBytes seg.emitted

/-- The opcode bytes of the instruction (its source payload, before padding). -/
abbrev PadSeg.opcode {width : Nat} [NeZero width] (seg : PadSeg width) : List (BitVec 8) :=
  lineBytes seg.source

/-- The trailing native padding bytes of the instruction: the excess of the
emitted payload over its opcode bytes. -/
abbrev PadSeg.padding {width : Nat} [NeZero width] (seg : PadSeg width) : List (BitVec 8) :=
  seg.payload.drop seg.opcode.length

/-- Number of bytes the instruction occupies in the padded image. -/
abbrev PadSeg.size {width : Nat} [NeZero width] (seg : PadSeg width) : Nat := seg.payload.length

/-- Number of trailing native padding bytes. -/
abbrev PadSeg.paddingLen {width : Nat} [NeZero width] (seg : PadSeg width) : Nat :=
  seg.padding.length

/-- The instructions of one section, each tagged with its section id.  Labels
are not instructions and carry no bytes. -/
def sectionInsts {width : Nat} [NeZero width] (sec : NativeCode width) :
    List (Nat × NativeLine width) :=
  sec.lines.filterMap (fun line =>
    if isLabelHOL line then none else some (sec.sectionId, line))

/-- The instructions of a whole code with their section ids, in emission order. -/
def codeInsts {width : Nat} [NeZero width] (code : List (NativeCode width)) :
    List (Nat × NativeLine width) := (code.map sectionInsts).flatten

theorem codeInsts_cons {width : Nat} [NeZero width] (sec : NativeCode width)
    (rest : List (NativeCode width)) :
    codeInsts (sec :: rest) = sectionInsts sec ++ codeInsts rest := rfl

/-- Scanning the emitted instruction stream against the source instruction
stream: each source instruction is paired with the emitted instruction at the
same instruction index, and the byte offset advances by the emitted size. -/
def scanInsts {width : Nat} [NeZero width] (base : Nat) :
    List (Nat × NativeLine width) → List (NativeLine width) → List (PadSeg width)
  | [], _ => []
  | _ :: _, [] => []
  | (sid, line) :: lines, emit :: emits =>
      ⟨sid, line, emit, base⟩ :: scanInsts (base + (lineBytes emit).length) lines emits

/-- The native padding scanner: walk the actual padded code `padded` and the
unpadded code `source` in lock step over their instruction streams, from byte
offset `base`, and return one segment per emitted instruction. -/
def scanCode {width : Nat} [NeZero width] (base : Nat)
    (source padded : List (NativeCode width)) : List (PadSeg width) :=
  scanInsts base (codeInsts source) (insts padded)

/-- `filterMap` and `filter` select the same lines. -/
theorem filterMap_fst_snd {width : Nat} [NeZero width] (sid : Nat)
    (lines : List (NativeLine width)) :
    (lines.filterMap (fun line => if isLabelHOL line then none else some (sid, line))).map
        Prod.snd = lines.filter notLabel := by
  induction lines with
  | nil => rfl
  | cons line lines ih =>
    cases h : isLabelHOL line <;> simp [List.filterMap, notLabel, h, ih]

theorem sectionInsts_snd {width : Nat} [NeZero width] (sec : NativeCode width) :
    (sectionInsts sec).map Prod.snd = sec.lines.filter notLabel :=
  filterMap_fst_snd sec.sectionId sec.lines

/-- The section-tagged instruction stream projects onto the instruction stream. -/
theorem codeInsts_snd {width : Nat} [NeZero width] (code : List (NativeCode width)) :
    (codeInsts code).map Prod.snd = insts code := by
  induction code with
  | nil => rfl
  | cons sec rest ih =>
    obtain ⟨sid, lines⟩ := sec
    simp only [codeInsts_cons, List.map_append, sectionInsts_snd, insts_cons, ih]

/-- Equal-length instruction streams are scanned back exactly.

This is proved without classical reasoning: the two impossible-length cases are
discharged by `omega` on the *normalised* length equation rather than by full
`simp at hlen`, which would close the goal through a `Decidable`-driven
contradiction and drag `Classical.choice` into every downstream certificate. -/
theorem scanInsts_maps {width : Nat} [NeZero width] (base : Nat)
    (source : List (Nat × NativeLine width)) (emits : List (NativeLine width))
    (hlen : source.length = emits.length) :
    (scanInsts base source emits).map PadSeg.source = source.map Prod.snd ∧
      (scanInsts base source emits).map PadSeg.emitted = emits := by
  induction source generalizing base emits with
  | nil =>
    cases emits with
    | nil => exact ⟨rfl, rfl⟩
    | cons e es =>
      simp only [List.length_nil, List.length_cons] at hlen
      exact absurd hlen (by omega)
  | cons pair source ih =>
    obtain ⟨sid, line⟩ := pair
    cases emits with
    | nil =>
      simp only [List.length_cons, List.length_nil] at hlen
      exact absurd hlen (by omega)
    | cons e es =>
      have hlen' : source.length = es.length := by
        simp only [List.length_cons] at hlen; omega
      obtain ⟨hsrc, hem⟩ := ih (base + (lineBytes e).length) es hlen'
      exact ⟨by simp only [scanInsts, List.map_cons, hsrc],
             by simp only [scanInsts, List.map_cons, hem]⟩

/-- The padded section of a source section is line-for-line similar to it:
`padCode` only appends nop bytes and resets label lengths. -/
theorem linesRel_padSection {width : Nat} [NeZero width] (nop : List (BitVec 8))
    (lines : List (NativeLine width)) : LinesRel lineSimilar lines (padSection nop lines []) :=
  lineSimilar_padSection nop lines [] lines (linesRel_refl lines)

/-- Similar line lists have equally many instructions. -/
theorem linesRel_filter_length {width : Nat} [NeZero width]
    {lines emits : List (NativeLine width)} (rel : LinesRel lineSimilar lines emits) :
    (lines.filter notLabel).length = (emits.filter notLabel).length := by
  induction rel with
  | nil => rfl
  | @cons line line' lines emits hsimilar htail ih =>
    have hlabel : isLabelHOL line = isLabelHOL line' := lineSimilar_isLabelHOL hsimilar
    have hfl : notLabel line = notLabel line' := by simp [notLabel, hlabel]
    rw [List.filter_cons, List.filter_cons, ← hfl]
    cases h : isLabelHOL line <;> simp [notLabel, h, ih]

/-- Padding preserves the number of instructions of a code. -/
theorem insts_padCode_length {width : Nat} [NeZero width] (nop : List (BitVec 8)) :
    ∀ source : List (NativeCode width),
      (insts source).length = (insts (padCode nop source)).length
  | [] => rfl
  | ⟨sid, lines⟩ :: rest => by
    rw [insts_cons, padCode, insts_cons, List.length_append, List.length_append,
      ← insts_padCode_length nop rest]
    congr 1
    -- the instruction count of a section is preserved by `padSection`
    have hsec : (sectionInsts ⟨sid, lines⟩ : List (Nat × NativeLine width)).length =
        (lines.filter notLabel).length := by
      rw [← List.length_map (f := Prod.snd), sectionInsts_snd]
    show (lines.filter notLabel).length = ((padSection nop lines []).filter notLabel).length
    exact linesRel_filter_length (linesRel_padSection nop lines)

/-- The scanner's own output for the source/padded pair `padCode nop source`:
the instruction streams have the same length, so no instruction is dropped. -/
theorem scanInsts_padCode {width : Nat} [NeZero width] (nop : List (BitVec 8)) (base : Nat)
    (source : List (NativeCode width)) :
    (scanCode base source (padCode nop source)).map PadSeg.source =
        (codeInsts source).map Prod.snd ∧
      (scanCode base source (padCode nop source)).map PadSeg.emitted =
        insts (padCode nop source) := by
  have hlen : (codeInsts source).length = (insts (padCode nop source)).length := by
    rw [show (codeInsts source).length = (insts source).length by
      rw [← List.length_map (f := Prod.snd), codeInsts_snd]]
    exact insts_padCode_length nop source
  exact scanInsts_maps base _ _ hlen

/-! ## What the padding does to the bytes: `padCode` keeps every opcode as a
byte prefix of the emitted instruction. -/

/-- The bytes the source line carries are a prefix of the bytes the padded line
carries, and the label-ness agrees: `padCode` only appends nop bytes. -/
def PadKeeps {width : Nat} [NeZero width] (src pad : NativeLine width) : Prop :=
  isLabelHOL src = isLabelHOL pad ∧ lineBytes src <+: lineBytes pad

/-- Pointwise `PadKeeps` over two equally long line lists. -/
inductive PadsRel {width : Nat} [NeZero width] :
    List (NativeLine width) → List (NativeLine width) → Prop
  | nil : PadsRel [] []
  | cons {src pad : NativeLine width} {ss ps : List (NativeLine width)} :
      PadKeeps src pad → PadsRel ss ps → PadsRel (src :: ss) (pad :: ps)

theorem padKeeps_refl {width : Nat} [NeZero width] (line : NativeLine width) :
    PadKeeps line line := ⟨rfl, ⟨[], List.append_nil _⟩⟩

theorem padsRel_refl {width : Nat} [NeZero width] :
    ∀ lines : List (NativeLine width), PadsRel lines lines
  | [] => .nil
  | line :: lines => .cons (padKeeps_refl line) (padsRel_refl lines)

theorem padsRel_append {width : Nat} [NeZero width] {a b c d : List (NativeLine width)} :
    PadsRel a b → PadsRel c d → PadsRel (a ++ c) (b ++ d)
  | .nil, h => h
  | .cons hk ht, h => .cons hk (padsRel_append ht h)

theorem padsRel_reverse {width : Nat} [NeZero width] {a b : List (NativeLine width)} :
    PadsRel a b → PadsRel a.reverse b.reverse := by
  intro h
  induction h with
  | nil => exact .nil
  | cons hk ht ih => simpa using padsRel_append ih (.cons hk .nil)

theorem padsRel_unreverse {width : Nat} [NeZero width] {a b : List (NativeLine width)} :
    PadsRel a.reverse b.reverse → PadsRel a b := by
  intro h
  have := padsRel_reverse h
  simpa using this

theorem padKeeps_trans {width : Nat} [NeZero width] {a b c : NativeLine width}
    (hab : PadKeeps a b) (hbc : PadKeeps b c) : PadKeeps a c :=
  ⟨hab.1.trans hbc.1, hab.2.trans hbc.2⟩

theorem padsRel_trans {width : Nat} [NeZero width] {a b c : List (NativeLine width)} :
    PadsRel a b → PadsRel b c → PadsRel a c
  | .nil, h => h
  | .cons hk ht, .cons hk' ht' => .cons (padKeeps_trans hk hk') (padsRel_trans ht ht')

theorem padsRel_filter {width : Nat} [NeZero width] {a b : List (NativeLine width)}
    (rel : PadsRel a b) (p : NativeLine width → Bool)
    (hcompat : ∀ src pad, PadKeeps src pad → p src = p pad) :
    PadsRel (a.filter p) (b.filter p) := by
  induction rel with
  | nil => exact .nil
  | @cons src pad ss ps hk ht ih =>
    rw [List.filter_cons, List.filter_cons, hcompat src pad hk]
    cases hp : p pad with
    | true => simp only [if_true]; exact .cons hk ih
    | false => simp only [Bool.false_eq_true, if_false]; exact ih

/-- The recovered source line and emitted line at the same index are
`PadKeeps`-related. -/
theorem padsRel_getElem? {width : Nat} [NeZero width] {a b : List (NativeLine width)}
    (rel : PadsRel a b) : ∀ (i : Nat) (src pad : NativeLine width),
      a[i]? = some src → b[i]? = some pad → PadKeeps src pad := by
  induction rel with
  | nil => intro i src pad hs hp; simp at hs
  | @cons src0 pad0 ss ps hk ht ih =>
    intro i src pad hs hp
    cases i with
    | zero =>
      rw [List.getElem?_cons_zero] at hs hp
      cases hs; cases hp
      exact hk
    | succ i =>
      rw [List.getElem?_cons_succ] at hs hp
      exact ih i src pad hs hp

/-- `padBytes` extends its input: padding is only ever appended. -/
theorem padBytes_prefix {α : Type} (bytes : List α) (len : Nat) (nop : List α) :
    bytes <+: padBytes bytes len nop := by
  rw [padBytes]
  split
  · exact ⟨[], List.append_nil _⟩
  · rename_i h
    have hlt : bytes.length ≤ len := by omega
    rw [List.prefix_iff_eq_take, List.take_take, Nat.min_eq_left hlt, List.take_left]

/-- `addNop` appends one nop chunk to the last instruction of the accumulator. -/
theorem addNop_padsRel {width : Nat} [NeZero width] (nop : List (BitVec 8)) :
    ∀ lines : List (NativeLine width), PadsRel lines (addNop nop lines)
  | [] => .nil
  | .label a b c :: xs => .cons ⟨rfl, ⟨[], List.append_nil _⟩⟩ (addNop_padsRel nop xs)
  | .asm a bytes len :: xs => .cons ⟨rfl, ⟨nop, rfl⟩⟩ (padsRel_refl xs)
  | .labAsm a w bytes len :: xs => .cons ⟨rfl, ⟨nop, rfl⟩⟩ (padsRel_refl xs)

theorem labelKeeps {width : Nat} [NeZero width] (a b len : Nat) :
    PadKeeps (.label a b len : NativeLine width) (.label a b 0) :=
  ⟨rfl, ⟨[], List.append_nil _⟩⟩

theorem asmKeeps {width : Nat} [NeZero width] (a : AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
    (bytes : List (BitVec 8)) (len : Nat) (nop : List (BitVec 8)) :
    PadKeeps (.asm a bytes len : NativeLine width) (.asm a (padBytes bytes len nop) len) :=
  ⟨rfl, padBytes_prefix bytes len nop⟩

theorem labAsmKeeps {width : Nat} [NeZero width] (a : AsmWithLab HolCmp (HolRegImm width) MlString)
    (w : BitVec width) (bytes : List (BitVec 8)) (len : Nat) (nop : List (BitVec 8)) :
    PadKeeps (.labAsm a w bytes len : NativeLine width)
      (.labAsm a w (padBytes bytes len nop) len) :=
  ⟨rfl, padBytes_prefix bytes len nop⟩

/-- `padSection` keeps every line of the accumulator and of the source, with the
source lines in order and the accumulator lines last-first (its `REVERSE aux`
shape), each as a byte prefix of the padded line. -/
theorem padSection_padsRel {width : Nat} [NeZero width] (nop : List (BitVec 8)) :
    ∀ (lines aux : List (NativeLine width)),
      PadsRel (lines.reverse ++ aux) ((padSection nop lines aux).reverse)
  | [], aux => by
    have h : PadsRel aux aux := padsRel_refl aux
    simpa [padSection] using h
  | .label a b len :: xs, aux => by
    have ih := padSection_padsRel nop xs
      (.label a b 0 :: (if len = 0 then aux else addNop nop aux))
    have hpart : PadsRel aux (if len = 0 then aux else addNop nop aux) := by
      by_cases hz : len = 0
      · rw [if_pos hz]; exact padsRel_refl aux
      · rw [if_neg hz]; exact addNop_padsRel nop aux
    have h1 : PadsRel ((.label a b len :: xs).reverse ++ aux)
        (xs.reverse ++ (.label a b 0 :: (if len = 0 then aux else addNop nop aux))) := by
      rw [List.reverse_cons, List.append_assoc]
      exact padsRel_append (padsRel_refl xs.reverse) (.cons (labelKeeps a b len) hpart)
    have h2 := padsRel_trans h1 ih
    simpa only [padSection] using h2
  | .asm a bytes len :: xs, aux => by
    have ih := padSection_padsRel nop xs (.asm a (padBytes bytes len nop) len :: aux)
    have h1 : PadsRel ((.asm a bytes len :: xs).reverse ++ aux)
        (xs.reverse ++ (.asm a (padBytes bytes len nop) len :: aux)) := by
      rw [List.reverse_cons, List.append_assoc]
      exact padsRel_append (padsRel_refl xs.reverse) (.cons (asmKeeps a bytes len nop) (padsRel_refl aux))
    have h2 := padsRel_trans h1 ih
    simpa only [padSection] using h2
  | .labAsm a w bytes len :: xs, aux => by
    have ih := padSection_padsRel nop xs (.labAsm a w (padBytes bytes len nop) len :: aux)
    have h1 : PadsRel ((.labAsm a w bytes len :: xs).reverse ++ aux)
        (xs.reverse ++ (.labAsm a w (padBytes bytes len nop) len :: aux)) := by
      rw [List.reverse_cons, List.append_assoc]
      exact padsRel_append (padsRel_refl xs.reverse)
        (.cons (labAsmKeeps a w bytes len nop) (padsRel_refl aux))
    have h2 := padsRel_trans h1 ih
    simpa only [padSection] using h2

/-- The padded section keeps every source line's bytes as a prefix. -/
theorem padSection_keeps {width : Nat} [NeZero width] (nop : List (BitVec 8))
    (lines : List (NativeLine width)) : PadsRel lines (padSection nop lines []) := by
  have h := padSection_padsRel nop lines []
  rw [List.append_nil] at h
  exact padsRel_unreverse h

/-- The whole padded code keeps every instruction of the source stream. -/
theorem padCode_padsRel {width : Nat} [NeZero width] (nop : List (BitVec 8)) :
    ∀ code : List (NativeCode width), PadsRel (insts code) (insts (padCode nop code))
  | [] => .nil
  | ⟨sid, lines⟩ :: rest => by
    rw [insts_cons, padCode, insts_cons]
    exact padsRel_append
      (padsRel_filter (padSection_keeps nop lines) notLabel
        (fun _ _ hk => by simp [notLabel, hk.1]))
      (padCode_padsRel nop rest)

/-! ## The certificate -/

/-- The recorded offsets are contiguous from `base` and advance by the padded
size of each instruction. -/
inductive OffsetChain {width : Nat} [NeZero width] : Nat → List (PadSeg width) → Prop
  | nil (base : Nat) : OffsetChain base []
  | cons {base : Nat} {seg : PadSeg width} {segs : List (PadSeg width)} :
      seg.offset = base → OffsetChain (base + (lineBytes seg.emitted).length) segs →
        OffsetChain base (seg :: segs)

theorem offsetChain_scanInsts {width : Nat} [NeZero width] (base : Nat)
    (source : List (Nat × NativeLine width)) (emits : List (NativeLine width)) :
    OffsetChain base (scanInsts base source emits) := by
  revert base emits
  induction source with
  | nil => intro base emits; exact .nil base
  | cons pair source ih =>
    obtain ⟨sid, line⟩ := pair
    intro base emits
    cases emits with
    | nil => exact .nil base
    | cons e es => exact .cons rfl (ih (base + (lineBytes e).length) es)

/-- Every recorded segment starts inside the padded image. -/
theorem offsetChain_bound {width : Nat} [NeZero width] {base : Nat} {segs : List (PadSeg width)}
    (chain : OffsetChain base segs) :
    ∀ seg ∈ segs, seg.offset + (lineBytes seg.emitted).length ≤
      base + (segs.map (fun s => (lineBytes s.emitted).length)).sum := by
  induction chain with
  | nil => intro seg hmem; simp at hmem
  | @cons base seg0 segs hoff htail ih =>
    intro seg hmem
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hmem with rfl | hmem
    · omega
    · have := ih seg hmem
      omega

/-- A padding certificate for the source/padded code pair.  Every field is a
proven fact about the data; the scanner produces the whole structure. -/
structure PadCertificate (width : Nat) [NeZero width] where
  /-- The nop chunk `padCode` repeats. -/
  nop : List (BitVec 8)
  /-- Byte offset the scan starts from. -/
  base : Nat
  /-- The unpadded code. -/
  source : List (NativeCode width)
  /-- The padded code actually emitted. -/
  padded : List (NativeCode width)
  /-- The scan result. -/
  segs : List (PadSeg width)
  /-- The padded code is the actual `padCode` image of the source. -/
  padded_eq : padded = padCode nop source
  /-- The segment table is the scanner's own output. -/
  scanned : segs = scanCode base source padded
  /-- Every emitted instruction is covered: no segment is dropped. -/
  complete : segs.length = (insts padded).length
  /-- Offsets are contiguous from `base`, advancing by padded sizes. -/
  chain : OffsetChain base segs
  /-- The recorded source instructions are the source instruction stream. -/
  sources_eq : segs.map PadSeg.source = insts source
  /-- The recorded emitted lines are the padded instruction stream. -/
  emitted_eq : segs.map PadSeg.emitted = insts padded
  /-- Each opcode's padding is accounted for: the source bytes are a prefix of
      the emitted bytes, so the extra bytes are exactly the native padding. -/
  padding_accounted : PadsRel (insts source) (insts padded)
  /-- The logical byte stream is the concatenation of the per-opcode segments. -/
  opcode_stream : (segs.map PadSeg.opcode).flatten =
    ((insts source).map lineBytes).flatten
  /-- The padded byte stream is the concatenation of the per-emitted-instruction
      segments: the actual padded image is their concatenation. -/
  payload_stream : (segs.map PadSeg.payload).flatten =
    ((insts padded).map lineBytes).flatten
  /-- Lengths agree: the padded image is `base` plus the sum of the segment sizes. -/
  lengths_agree : (segs.map (fun s => s.size)).sum =
    ((insts padded).map lineBytes).flatten.length

/-- **The scanner returns a certificate for its own output.** -/
def PadCertificate.ofScan {width : Nat} [NeZero width] (nop : List (BitVec 8))
    (base : Nat) (source : List (NativeCode width)) (padded : List (NativeCode width))
    (padded_eq : padded = padCode nop source) : PadCertificate width := by
  have hscan := scanInsts_padCode nop base source
  have hpad : (scanCode base source padded).map PadSeg.source = (codeInsts source).map Prod.snd ∧
      (scanCode base source padded).map PadSeg.emitted = insts padded := by
    rw [padded_eq]
    exact hscan
  have hsrc : (scanCode base source padded).map PadSeg.source = insts source := by
    rw [hpad.1, codeInsts_snd]
  have hem : (scanCode base source padded).map PadSeg.emitted = insts padded := hpad.2
  exact
    { nop := nop
      base := base
      source := source
      padded := padded
      segs := scanCode base source padded
      padded_eq := padded_eq
      scanned := rfl
      complete := by
        rw [← List.length_map (f := PadSeg.emitted), hem]
      chain := offsetChain_scanInsts base (codeInsts source) (insts padded)
      sources_eq := hsrc
      emitted_eq := hem
      padding_accounted := by rw [padded_eq]; exact padCode_padsRel nop source
      opcode_stream := by rw [← hsrc, List.map_map]; rfl
      payload_stream := by rw [← hem, List.map_map]; rfl
      lengths_agree := by
        rw [← hem, List.map_map, List.length_flatten, List.map_map]
        rfl }

/-! ## The transfer

The scanner certificate transports a source fetch to the padded code.  The
code-level similarity is *derived* (never assumed) by the existing
`codeSimilar_padCode` theorem, and the fetch step reuses the existing bridge
`codeSimilar_asmFetchAux`; the scanner contributes the offset, the padded bytes
and the opcode the padded instruction belongs to. -/

/-- The source/padded code pair of a certificate is `codeSimilar`: this is the
existing padding similarity theorem instantiated at the certificate's own data. -/
theorem PadCertificate.codeSimilar {width : Nat} [NeZero width] (cert : PadCertificate width) :
    codeSimilar cert.source cert.padded := by
  rw [cert.padded_eq]
  exact codeSimilar_padCode cert.source cert.source cert.nop (codeSimilar_refl cert.source)

theorem optionRel_some {α β : Type} {rel : α → β → Prop} {a : α} {y : Option β} :
    Option.Rel rel (some a) y → ∃ b, y = some b ∧ rel a b := by
  intro h
  cases y with
  | none => cases h
  | some b =>
    exact ⟨b, rfl, by cases h; assumption⟩

/-- Every recorded segment's opcode bytes are a prefix of its emitted bytes. -/
theorem PadCertificate.segment_keeps {width : Nat} [NeZero width] (cert : PadCertificate width)
    {seg : PadSeg width} (hmem : seg ∈ cert.segs) :
    lineBytes seg.source <+: lineBytes seg.emitted := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
  have h1 : (cert.segs.map PadSeg.source)[i]? = some seg.source := by
    rw [List.getElem?_map, hi]; rfl
  have h2 : (cert.segs.map PadSeg.emitted)[i]? = some seg.emitted := by
    rw [List.getElem?_map, hi]; rfl
  rw [cert.sources_eq] at h1
  rw [cert.emitted_eq] at h2
  exact (padsRel_getElem? cert.padding_accounted i seg.source seg.emitted h1 h2).2

/-- **The transfer.**  If the source code fetches instruction `pc` (with
`asmFetchAux`) and the scanner's certificate records, for that same instruction,
the padded segment at its byte offset, then the padded code fetches the same
instruction position — a `lineSimilar` instruction — and the fetched padded
bytes are exactly the recorded opcode bytes followed by the recorded native
padding, starting at the scanner-computed offset. -/
def PaddedFetch {width : Nat} [NeZero width] (cert : PadCertificate width) (pc : Nat)
    (line : NativeLine width) : Prop :=
  ∃ seg ∈ cert.segs, ∃ line' : NativeLine width,
    asmFetchAux pc cert.padded = some line' ∧
    lineSimilar line line' ∧
    seg.source = line ∧
    seg.emitted = line' ∧
    (cert.segs.map PadSeg.offset)[pc]? = some seg.offset ∧
    (cert.segs.map PadSeg.payload)[pc]? = some (lineBytes line') ∧
    lineBytes line <+: lineBytes line' ∧
    seg.offset + (lineBytes line').length ≤
      cert.base + ((insts cert.padded).map lineBytes).flatten.length

theorem padScan_fetch_transfer {width : Nat} [NeZero width] (cert : PadCertificate width)
    (pc : Nat) (line : NativeLine width) (fetch : asmFetchAux pc cert.source = some line) :
    PaddedFetch cert pc line := by
  -- code similarity of the certificate's own pair, derived by the existing theorem
  have hsim : codeSimilar cert.source (padCode cert.nop cert.source) := by
    rw [← cert.padded_eq]
    exact cert.codeSimilar
  have hrel := codeSimilar_asmFetchAux pc cert.source (padCode cert.nop cert.source) hsim
  rw [← cert.padded_eq] at hrel
  rw [fetch] at hrel
  obtain ⟨line', hfetch', hs⟩ := optionRel_some hrel
  -- the fetched instructions are the entries of the two instruction streams
  have hsrc : (insts cert.source)[pc]? = some line := by
    rw [← asmFetchAux_eq_insts pc cert.source, fetch]
  have hpadded : (insts cert.padded)[pc]? = some line' := by
    rw [← asmFetchAux_eq_insts pc cert.padded, hfetch']
  rw [← cert.sources_eq] at hsrc
  rw [← cert.emitted_eq] at hpadded
  rw [List.getElem?_map] at hsrc hpadded
  cases hpc : cert.segs[pc]? with
  | none => rw [hpc] at hsrc; simp at hsrc
  | some seg =>
    rw [hpc] at hsrc hpadded
    simp only [Option.map, Option.some.injEq] at hsrc hpadded
    have hmem : seg ∈ cert.segs := List.mem_iff_getElem?.mpr ⟨pc, hpc⟩
    obtain rfl : line' = seg.emitted := hpadded.symm
    obtain rfl : line = seg.source := hsrc.symm
    refine ⟨seg, hmem, seg.emitted, hfetch', hs, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · rw [List.getElem?_map, hpc]; rfl
    · rw [List.getElem?_map, hpc]; rfl
    · exact cert.segment_keeps hmem
    · rw [← cert.lengths_agree]
      exact offsetChain_bound cert.chain seg hmem

/-! ## The transfer instantiated at the artifact, and concrete scanner runs

The scanner is a computable function of the concrete code objects, so the
certificate below is literally `scanCode` applied to the guest's own final
code, and the scan can be *evaluated* on the artifact's sections. -/

section Artifact

open InitECandidate.Proofs.BackendStages
open Flapjack.Compiler.Encoders.RiscV.Target

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000

/-- The nop chunk `padCode` repeats in the final assembly. -/
def paddingNop : List (BitVec 8) := riscvConfig.encode (.inst .skip)

/-- **The padding byte is a computed constant, not a chosen one.**  `padCode`
pads with the emitter's own `.skip` image, and the RISC-V backend lowers
`.skip` to `riscvEncodeFail` -- the architectural NOP `addi x0, x0, 0`, whose
32-bit word `0x00000013` `riscvEncode` emits little-endian.  `decide_cbv` runs
the emitter on the artifact's real configuration. -/
theorem paddingNop_eq : paddingNop = [0x13, 0x00, 0x00, 0x00] := by
  decide_cbv

/-- **The certificate of the guest's actual final code.**  `Final.final0` is the
pre-padding object and `Final.padded0` its `padCode` image, which
`Final.padding0_eq` proves; everything else in the certificate is computed by
the scanner and proven about that computation. -/
def padded0Certificate : PadCertificate 64 :=
  PadCertificate.ofScan paddingNop 0 Final.final0 Final.padded0 Final.padding0_eq

/-- **The padded-offset transfer on the guest's own final code.** -/
theorem padded0_fetch_transfer (pc : Nat) (line : NativeLine 64)
    (fetch : asmFetchAux pc Final.final0 = some line) :
    PaddedFetch padded0Certificate pc line :=
  padScan_fetch_transfer padded0Certificate pc line fetch

/-- The source/padded pair of that certificate is `codeSimilar`. -/
theorem padded0_codeSimilar : codeSimilar Final.final0 Final.padded0 :=
  padded0Certificate.codeSimilar

/-- Artifact section 597 is padded by the scanner's nop chunk. -/
theorem section597_pad :
    LabToTarget.padCode paddingNop ([FinalReencode597] : List (NativeCode 64)) = [Padded597] := by
  show (⟨FinalReencode597.sectionId,
        LabToTarget.padSection (riscvConfig.encode (.inst .skip)) FinalReencode597.lines []⟩ :
      NativeCode 64) :: LabToTarget.padCode (riscvConfig.encode (.inst .skip)) [] = [Padded597]
  rw [Padded597_eq]
  rfl

/-- **A concrete scan of the artifact.**  In section 597 `padCode` really pads:
two instructions have 4 opcode bytes and recorded length 8, and the scanner
reports, for each, its byte offset in the padded section, its opcode length and
its padded length.  This is `decide_cbv`: the numbers are computed by the
scanner running on the artifact's concrete code. -/
theorem section597_scan_segments :
    ((scanCode 0 ([FinalReencode597] : List (NativeCode 64)) [Padded597]).filter
        (fun s => !(s.paddingLen == 0))).map
        (fun s => (s.offset, s.opcode.length, s.payload.length)) =
      [(20, 4, 8), (3848, 4, 8)] := by
  decide_cbv

/-- The scanner certificate of that same artifact section. -/
def section597Certificate : PadCertificate 64 :=
  PadCertificate.ofScan paddingNop 0 [FinalReencode597] [Padded597] section597_pad

/-- The padded-offset transfer on that artifact section. -/
theorem section597_fetch_transfer (pc : Nat) (line : NativeLine 64)
    (fetch : asmFetchAux pc ([FinalReencode597] : List (NativeCode 64)) = some line) :
    PaddedFetch section597Certificate pc line :=
  padScan_fetch_transfer section597Certificate pc line fetch

/-! ## The numeric identity behind the padding bound -/

/-- The padding an instruction pays is exactly the excess of its emitted
payload over its opcode bytes.  With the encoder's minimum length this turns a
recorded length of at most four bytes into a padding of zero. -/
theorem PadSeg.paddingLen_eq_of_prefix {width : Nat} [NeZero width] (seg : PadSeg width)
    (h : lineBytes seg.source <+: lineBytes seg.emitted) :
    seg.paddingLen = (lineBytes seg.emitted).length - (lineBytes seg.source).length := by
  have hle : (lineBytes seg.source).length ≤ (lineBytes seg.emitted).length :=
    List.IsPrefix.length_le h
  simp only [PadSeg.paddingLen, PadSeg.padding, PadSeg.payload, PadSeg.opcode,
    List.length_drop]

/-- A scanned segment whose emitted bytes exceed its opcode bytes by at most
`b` pays at most `b` padding bytes. -/
theorem PadSeg.paddingLen_le_of_length_le {width : Nat} [NeZero width] (seg : PadSeg width)
    (b : Nat) (h : lineBytes seg.source <+: lineBytes seg.emitted)
    (hb : (lineBytes seg.emitted).length ≤ (lineBytes seg.source).length + b) :
    seg.paddingLen ≤ b := by
  rw [seg.paddingLen_eq_of_prefix h]
  omega

/-- **A certified numeric padding bound on a real artifact section.**  Every
instruction the scanner records for section 597 -- one of the artifact sections
where `padCode` really pads -- carries at most one four-byte nop chunk.  The
bound is a kernel computation over the artifact's own code (`decide_cbv`). -/
theorem section597_padding_bound :
    (scanCode 0 ([FinalReencode597] : List (NativeCode 64)) [Padded597]).all
      (fun s => decide (s.paddingLen ≤ 4)) = true := by
  decide_cbv

end Artifact

/-! ## The numeric per-instruction padding bound

`padSection` passes a source line's recorded length `len` straight to `padBytes`,
so the padding a scanned instruction carries is exactly the *slack* of the line it
came from: the excess of that line's recorded length over the bytes the line
actually holds.  These are the numeric facts the certificate above leaves
implicit -- neither `Padding.lean` nor this scan states the `recordedLen` /
`lineBytes` relation, so it is proved here. -/

/-- The recorded length field of a line. -/
def lineRecLen {width : Nat} [NeZero width] : NativeLine width → Nat
  | .label _ _ l => l
  | .asm _ _ l => l
  | .labAsm _ _ _ l => l

/-- A line's byte slack: recorded length minus the bytes it actually carries.
`padCode` pads an instruction by exactly this slack. -/
def lineSlack {width : Nat} [NeZero width] (line : NativeLine width) : Nat :=
  lineRecLen line - (lineBytes line).length

/-- `padBytes` extends a byte list to exactly `max bytes.length len` bytes: it
neither truncates nor overshoots, for any nonempty nop chunk. -/
theorem padBytes_length {α : Type} (bytes : List α) (len : Nat) (nop : List α)
    (hne : nop ≠ []) : (padBytes bytes len nop).length = max bytes.length len := by
  rw [padBytes]
  split
  · rename_i h
    omega
  · rename_i h
    have h1 : 1 ≤ nop.length := by
      cases nop with
      | nil => exact absurd rfl hne
      | cons x xs => simp
    have hge : ∀ m : Nat, m ≤ (List.replicate m nop).flatten.length := by
      intro m
      induction m with
      | zero => simp
      | succ k ih =>
        simp only [List.replicate_succ, List.flatten_cons, List.length_append]
        omega
    have hself : len ≤ (bytes ++ (List.replicate len nop).flatten).length := by
      rw [List.length_append]
      have := hge len
      omega
    have hsplit := List.take_append_drop len (bytes ++ (List.replicate len nop).flatten)
    have hlen : ((bytes ++ (List.replicate len nop).flatten).take len).length +
        ((bytes ++ (List.replicate len nop).flatten).drop len).length =
        (bytes ++ (List.replicate len nop).flatten).length := by
      rw [← List.length_append, hsplit]
    rw [List.length_drop] at hlen
    omega

/-- **The padding of a padded `Asm` instruction is its source line's slack.**
`padSection` emits `padBytes bytes len nop` with the recorded length unchanged, so
the bytes it adds are exactly `len - bytes.length` -- zero when the line already
holds its recorded length -- and the emitted line's own slack is zero. -/
theorem padSection_asm_padding {width : Nat} [NeZero width] (nop : List (BitVec 8))
    (hne : nop ≠ []) (a : AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
    (bytes : List (BitVec 8)) (len : Nat) :
    (lineBytes (.asm a (padBytes bytes len nop) len)).length - bytes.length =
        lineSlack (.asm a bytes len) ∧
      lineSlack (.asm a (padBytes bytes len nop) len) = 0 := by
  have h := padBytes_length bytes len nop hne
  constructor
  · show (padBytes bytes len nop).length - bytes.length = len - bytes.length
    omega
  · show len - (padBytes bytes len nop).length = 0
    omega

/-- The same for a re-encoded `LabAsm` instruction. -/
theorem padSection_labAsm_padding {width : Nat} [NeZero width] (nop : List (BitVec 8))
    (hne : nop ≠ []) (a : AsmWithLab HolCmp (HolRegImm width) MlString)
    (w : BitVec width) (bytes : List (BitVec 8)) (len : Nat) :
    (lineBytes (.labAsm a w (padBytes bytes len nop) len)).length - bytes.length =
        lineSlack (.labAsm a w bytes len) ∧
      lineSlack (.labAsm a w (padBytes bytes len nop) len) = 0 := by
  have h := padBytes_length bytes len nop hne
  constructor
  · show (padBytes bytes len nop).length - bytes.length = len - bytes.length
    omega
  · show len - (padBytes bytes len nop).length = 0
    omega

/-- The emitted padding chunk is one four-byte RISC-V word, so a line with no
slack is padded by a multiple of four bytes and never by more than that word. -/
theorem paddingNop_length : paddingNop.length = 4 := by
  rw [paddingNop_eq]
  rfl

/-! ### The remaining source-side obligation

`padSection_asm_padding`/`padSection_labAsm_padding` turn any bound on a source
line's *slack* into the padding of its image, so the whole-artifact numeric bound
reduces to a bound on the pre-padding code.  That bound is an encoding fact --
`encLinesAgain` passes `Asm` lines through unchanged, a re-encoded `LabAsm` line
takes `l1 = max bs.length l`, `linesUpdLabLen` gives each label length `0` or `1`,
and `addNop` appends exactly one nop chunk -- and it is stated nowhere yet. -/

/-- **Open obligation: the source-side slack bound.**  Every instruction line of
the artifact's pre-padding code carries at most `B` bytes of recorded slack.

This is the only missing premise: the segment-level form
`∀ seg ∈ padded0Certificate.segs,
 (lineBytes seg.emitted).length ≤ (lineBytes seg.source).length + B`
follows from it through `padSection_asm_padding`/`padSection_labAsm_padding`
plus one `addNop` chunk, and `PadSeg.paddingLen_le_of_length_le` then gives
`seg.paddingLen ≤ B` for every scanned segment.  It is *not* provable by
computation: reducing any artifact-wide projection of `Final.final0` (205014
instruction lines) overflows the stack, so it must be proved structurally about
`encLinesAgain`/`linesUpdLabLen`/`addNop`. -/
def SourceSlackBound (B : Nat) : Prop :=
  ∀ line ∈ insts InitECandidate.Proofs.BackendStages.Final.final0, lineSlack line ≤ B

#print axioms scanInsts_maps
#print axioms asmFetchAux_eq_insts
#print axioms scanInsts_padCode
#print axioms padSection_keeps
#print axioms padCode_padsRel
#print axioms offsetChain_scanInsts
#print axioms offsetChain_bound
#print axioms PadCertificate.ofScan
#print axioms PadCertificate.codeSimilar
#print axioms PadCertificate.segment_keeps
#print axioms padScan_fetch_transfer
#print axioms padded0_fetch_transfer
#print axioms padded0_codeSimilar
#print axioms paddingNop_eq
#print axioms paddingNop_length
#print axioms lineRecLen
#print axioms lineSlack
#print axioms padBytes_length
#print axioms padSection_asm_padding
#print axioms padSection_labAsm_padding
#print axioms SourceSlackBound
#print axioms PadSeg.paddingLen_eq_of_prefix
#print axioms PadSeg.paddingLen_le_of_length_le
#print axioms section597_pad
#print axioms section597_scan_segments
#print axioms section597_padding_bound
#print axioms section597_fetch_transfer


/-- Recorded span check: a line's recorded length exceeds its byte length by at
most `b`.  Labels carry no bytes. -/
def padSlackOK {width : Nat} [NeZero width] (b : Nat) (line : NativeLine width) : Bool :=
  match line with
  | .label _ _ _ => true
  | .asm _ bytes len => decide (len ≤ bytes.length + b)
  | .labAsm _ _ bytes len => decide (len ≤ bytes.length + b)

/-- Section-wise span bounds compose into a bound on the whole instruction
stream.  The filtered line lists are the per-section inputs, so no filter lemma
is needed. -/
theorem insts_all_of_sections {width : Nat} [NeZero width] (b : Nat) :
    forall (secs : List (NativeCode width)),
      (forall s, s ∈ secs -> (List.filter notLabel s.lines).all (padSlackOK b) = true) ->
      (insts secs).all (padSlackOK b) = true := by
  intro secs
  induction secs with
  | nil => intro _; rfl
  | cons sec rest ih =>
      intro h
      obtain ⟨sid, lines⟩ := sec
      rw [insts_cons, List.all_append, Bool.and_eq_true]
      exact ⟨h ⟨sid, lines⟩ (by simp),
             ih (by intro s hs; exact h s (by simp [hs]))⟩



/-- Labels never appear in a section's instruction stream. -/
theorem label_not_mem_insts {width : Nat} [NeZero width] (a b l : Nat)
    (secs : List (NativeCode width)) :
    (Line.label a b l : NativeLine width) ∉ insts secs := by
  induction secs with
  | nil =>
      intro h
      simp only [insts, List.map_nil, List.flatten_nil, List.not_mem_nil] at h
  | cons sec rest ih =>
      obtain ⟨sid, lines⟩ := sec
      intro h
      rw [insts_cons] at h
      rw [List.mem_append] at h
      rcases h with h | h
      · obtain ⟨-, hn⟩ := List.mem_filter.mp h
        simp only [notLabel, isLabelHOL] at hn
        exact Bool.noConfusion hn
      · exact ih h



/-- A padded line pays exactly the source line's slack, so a source slack of at
most four bytes is a padding of at most four bytes. -/
theorem pad_line_bytes_le {width : Nat} [NeZero width] (nop : List (BitVec 8))
    (hne : nop ≠ []) (a : AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
    (bytes : List (BitVec 8)) (len : Nat)
    (h : lineSlack (.asm a bytes len) ≤ 4) :
    (lineBytes (.asm a (padBytes bytes len nop) len)).length - bytes.length ≤ 4 := by
  have hp := (padSection_asm_padding nop hne a bytes len).1
  omega

end InitECandidate.Runtime.NativePadding
