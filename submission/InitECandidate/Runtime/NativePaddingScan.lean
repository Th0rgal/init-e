import InitECandidate.Proofs.BackendStages.Final
import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.Padding
import Flapjack.Compiler.Backend.LabToTarget.Navigation
import Flapjack.Compiler.Backend.LabToTarget.RemoveLabels

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

/-- Equal-length instruction streams are scanned back exactly. -/
theorem scanInsts_maps {width : Nat} [NeZero width] (base : Nat)
    (source : List (Nat × NativeLine width)) (emits : List (NativeLine width))
    (hlen : source.length = emits.length) :
    (scanInsts base source emits).map PadSeg.source = source.map Prod.snd ∧
      (scanInsts base source emits).map PadSeg.emitted = emits := by
  revert base emits hlen
  induction source with
  | nil =>
    intro base emits hlen
    cases emits with
    | nil => exact ⟨rfl, rfl⟩
    | cons e es => simp at hlen
  | cons pair source ih =>
    intro base emits hlen
    cases emits with
    | nil => simp at hlen
    | cons e es =>
      obtain ⟨sid, line⟩ := pair
      simp only [List.length_cons] at hlen
      obtain ⟨hsrc, hem⟩ := ih (base + (lineBytes e).length) es (by omega)
      simp only [scanInsts, List.map_cons]
      exact ⟨by simp [hsrc], by simp [hem]⟩

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

end InitECandidate.Runtime.NativePadding
