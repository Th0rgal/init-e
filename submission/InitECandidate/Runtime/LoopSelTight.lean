import InitECandidate.Runtime.WordIselTight
import InitECandidate.Runtime.LoopLeafSelPrice
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend

/-! A pattern-aware price of Loop expressions that bounds their exact selected
cost `selT` through `comp_exp`, `pull_exp` and `flatten_exp`: `TopAddr` is 72,
constant operands fold into immediates and constant-offset loads into the load,
where the selector does so. Other shapes fall back to the structural `fL`. -/

section Shapes
variable (c : Compiler.Encoders.Asm.AsmConfigExact 64)

open WordInst.ExecutablePullExp in
theorem pull_load (x : WordLangExpHOL (BitVec 64)) : pullExpExecutable (.load x) = .load (pullExpExecutable x) := by
  rw [pullExpExecutable]

open WordInst.ExecutablePullExp in
theorem pull_shift (s : Shift) (x y : WordLangExpHOL (BitVec 64)) :
    pullExpExecutable (.shift s x y) = .shift s (pullExpExecutable x) (pullExpExecutable y) := by
  rw [pullExpExecutable]

open WordInst.ExecutablePullExp in
theorem pull_sub2 (x y : WordLangExpHOL (BitVec 64)) :
    pullExpExecutable (.op .sub [x, y]) = WordInst.convertSub [pullExpExecutable x, pullExpExecutable y] := by
  rw [pullExpExecutable]; simp

open WordInst.ExecutablePullExp in
theorem pull_op2 (o : BinOp) (h : o ≠ .sub) (x y : WordLangExpHOL (BitVec 64)) :
    pullExpExecutable (.op o [x, y]) =
      optimizeNonSub o h (WordInst.pullOps o [pullExpExecutable x, pullExpExecutable y] []) := by
  rw [pullExpExecutable]; simp [h]

theorem flat_load (x : WordLangExpHOL (BitVec 64)) : WordInst.flattenExp (.load x) = .load (WordInst.flattenExp x) := by
  rw [WordInst.flattenExp]

theorem flat_shift (s : Shift) (x y : WordLangExpHOL (BitVec 64)) :
    WordInst.flattenExp (.shift s x y) = .shift s (WordInst.flattenExp x) (WordInst.flattenExp y) := by
  rw [WordInst.flattenExp]

theorem flat_sub2 (x y : WordLangExpHOL (BitVec 64)) :
    WordInst.flattenExp (.op .sub [x, y]) = .op .sub [WordInst.flattenExp x, WordInst.flattenExp y] := by
  rw [WordInst.flattenExp]; simp

theorem flat_op1 (o : BinOp) (h : o ≠ .sub) (x : WordLangExpHOL (BitVec 64)) :
    WordInst.flattenExp (.op o [x]) = WordInst.flattenExp x := by
  rw [WordInst.flattenExp]; simp [h]

theorem flat_op2 (o : BinOp) (h : o ≠ .sub) (x y : WordLangExpHOL (BitVec 64)) :
    WordInst.flattenExp (.op o [x, y]) = .op o [WordInst.flattenExp y, WordInst.flattenExp x] := by
  rw [WordInst.flattenExp]
  all_goals first | exact h | simp [flat_op1 o h]

theorem iselT_const (w : BitVec 64) : iselT c (.const w) = 24 := iselT.eq_3 c w
theorem iselT_var (v : Nat) : iselT c (.var v) = 24 := iselT.eq_4 c v
theorem iselT_lookup (st : WordStoreHOL) : iselT c (.lookup st) = 24 := iselT.eq_5 c st

theorem iselT_op_le (o : BinOp) (X Y : WordLangExpHOL (BitVec 64)) :
    iselT c (.op o [X, Y]) ≤ iselT c X + iselT c Y + 24 := by
  by_cases hc : ∃ w, Y = .const w
  · obtain ⟨w, rfl⟩ := hc
    rw [iselT.eq_6, iselT_const]; split_ifs <;> omega
  · rw [iselT.eq_7 c o X Y (fun w hw => hc ⟨w, hw⟩)]; split_ifs <;> omega

/-- Immediate-operand price of `op o [_, const w]`. -/
def immC (o : BinOp) (w : BitVec 64) : Nat :=
  if c.validImm (.inl o) w = true ∨ (o = .add ∧ c.validImm (.inl .sub) (-w) = true) then 24 else 48

theorem iselT_currHeap {e : WordLangExpHOL (BitVec 64)} (h : WordInst.isLookupCurrHeap e = true) :
    iselT c e = 24 := by
  cases e <;> simp [WordInst.isLookupCurrHeap] at h
  exact iselT_lookup c _

theorem iselT_op_const (o : BinOp) (X : WordLangExpHOL (BitVec 64)) (w : BitVec 64) :
    iselT c (.op o [X, .const w]) ≤ iselT c X + immC c o w := by
  rw [iselT.eq_6]; unfold immC
  split_ifs with h1
  · rw [iselT_currHeap c h1.1] <;> (try split_ifs) <;> omega
  all_goals first | omega | (simp_all <;> omega)

theorem iselT_op_add_le (e' : WordLangExpHOL (BitVec 64)) (w : BitVec 64) :
    iselT c e' ≤ iselT c (.op .add [e', .const w]) := by
  rw [iselT.eq_6]
  split_ifs with h1
  · rw [iselT_currHeap c h1.1]; omega
  all_goals omega

theorem iselT_load_le (X : WordLangExpHOL (BitVec 64)) : iselT c (.load X) ≤ iselT c X + 24 := by
  by_cases hp : ∃ e' w, X = .op .add [e', .const w]
  · obtain ⟨e', w, rfl⟩ := hp
    rw [iselT.eq_1]
    have := iselT_op_add_le c e' w
    split_ifs <;> omega
  · rw [iselT.eq_2 c X (fun e' w h => hp ⟨e', w, h⟩)]

theorem iselT_load_offset (X : WordLangExpHOL (BitVec 64)) (w : BitVec 64) (ok : WordInst.addrOffsetOk c w = true) :
    iselT c (.load (.op .add [X, .const w])) = iselT c X + 24 := by
  rw [iselT.eq_1]; simp [ok]

theorem iselT_shift_le (s : Shift) (X Y : WordLangExpHOL (BitVec 64)) :
    iselT c (.shift s X Y) ≤ iselT c X + iselT c Y + 28 := by
  by_cases hc : ∃ w, Y = .const w
  · obtain ⟨w, rfl⟩ := hc
    rw [iselT.eq_8]; split_ifs <;> omega
  · rw [iselT.eq_9 c s X Y (fun w hw => hc ⟨w, hw⟩)]

theorem iselT_shift_const (s : Shift) (X : WordLangExpHOL (BitVec 64)) (n : BitVec 64) :
    iselT c (.shift s X (.const n)) = if n.toNat < 64 then iselT c X + 24 else 24 := iselT.eq_8 c s X n


theorem iselCost_opc (o : BinOp) (e1 : WordLangExpHOL (BitVec 64)) (w : BitVec 64) :
    iselCost (.op o [e1, .const w]) = iselCost e1 + 48 := by
  rw [iselCost_op2]; simp

theorem iselT_le_iselCost (e : WordLangExpHOL (BitVec 64)) : iselT c e ≤ iselCost e := by
  refine (measure (sizeOf : WordLangExpHOL (BitVec 64) → Nat)).wf.induction (C := fun e =>
    iselT c e ≤ iselCost e) e ?_
  intro e ih
  cases e with
  | const w => rw [iselT_const]; simp
  | var v => rw [iselT_var]; simp
  | lookup st => rw [iselT_lookup]; simp
  | load x =>
    by_cases hp : ∃ e' w, x = .op .add [e', .const w]
    · obtain ⟨e', w, rfl⟩ := hp
      rw [iselT.eq_1, iselCost_load, iselCost_opc]
      have h1 := ih e' (by show sizeOf e' < _; simp; omega)
      have h2 := ih (.op .add [e', .const w]) (by show sizeOf _ < _; simp)
      rw [iselCost_opc] at h2
      split_ifs <;> omega
    · rw [iselT.eq_2 c x (fun e' w h => hp ⟨e', w, h⟩), iselCost_load]
      have := ih x (by show sizeOf x < _; simp); omega
  | op o ls =>
    rcases ls with _ | ⟨e1, _ | ⟨e2, _ | ⟨e3, rest⟩⟩⟩
    · rw [iselT.eq_10] <;> simp
    · rw [iselT.eq_10] <;> simp
    · have h1 := ih e1 (by show sizeOf e1 < _; simp; omega)
      have h2 := ih e2 (by show sizeOf e2 < _; simp; omega)
      rw [iselCost_op2]
      by_cases hc : ∃ w, e2 = .const w
      · obtain ⟨w, rfl⟩ := hc
        rw [iselT.eq_6]; simp only [iselCost_const] at h2 ⊢
        split_ifs <;> omega
      · rw [iselT.eq_7 c o e1 e2 (fun w hw => hc ⟨w, hw⟩)]; split_ifs <;> omega
    · rw [iselT.eq_10] <;> simp
  | shift s x y =>
    have h1 := ih x (by show sizeOf x < _; simp; omega)
    have h2 := ih y (by show sizeOf y < _; simp)
    rw [iselCost_shift]
    by_cases hc : ∃ w, y = .const w
    · obtain ⟨w, rfl⟩ := hc
      rw [iselT.eq_8]; split_ifs <;> omega
    · rw [iselT.eq_9 c s x y (fun w hw => hc ⟨w, hw⟩)]; omega

/-- The exact selected cost is within the structural Loop price. -/
theorem selT_le_fL (ctxt : Spt Nat) (e : HolLoopExp 64) : selT c (LoopToWord.compExpHOL ctxt e) ≤ fL e := by
  have h1 := iselT_le_iselCost c (WordInst.flattenExp (WordInst.ExecutablePullExp.pullExpExecutable
    (LoopToWord.compExpHOL ctxt e)))
  have h2 := iselCost_flatten (WordInst.ExecutablePullExp.pullExpExecutable (LoopToWord.compExpHOL ctxt e))
  have h3 := fW_pull (LoopToWord.compExpHOL ctxt e)
  rw [fW_compExp] at h3
  unfold selT; omega

theorem pullOps_two (o : BinOp) (X Y : WordLangExpHOL (BitVec 64)) (hX : ∀ ls, X ≠ .op o ls)
    (hY : ∀ ls, Y ≠ .op o ls) : WordInst.pullOps o [X, Y] [] = [Y, X] := by
  have hx : ∀ o' ls, X = .op o' ls → o ≠ o' := by rintro o' ls rfl rfl; exact hX ls rfl
  have hy : ∀ o' ls, Y = .op o' ls → o ≠ o' := by rintro o' ls rfl rfl; exact hY ls rfl
  cases X <;> cases Y <;> simp [WordInst.pullOps] <;> simp_all

theorem optimize_two (o : BinOp) (h : o ≠ .sub) (X Y : WordLangExpHOL (BitVec 64))
    (hX : WordInst.isConst X = false) (hY : WordInst.isConst Y = false) :
    WordInst.ExecutablePullExp.optimizeNonSub o h [Y, X] = .op o [X, Y] := by
  simp [WordInst.ExecutablePullExp.optimizeNonSub, holPartition, holPart, hX, hY]

theorem nonSubWordOp_one (o : BinOp) (h : o ≠ .sub) (w : BitVec 64) :
    WordInst.ExecutablePullExp.nonSubWordOp o h [w] = w := by
  cases o
  · simp [WordInst.ExecutablePullExp.nonSubWordOp]
  · exact absurd rfl h
  · show w &&& ~~~(0 : BitVec 64) = w
    have : (~~~(0 : BitVec 64)) = BitVec.allOnes 64 := by decide
    rw [this]; exact BitVec.and_allOnes
  · show w ||| (0 : BitVec 64) = w
    exact BitVec.or_zero
  · simp [WordInst.ExecutablePullExp.nonSubWordOp]

theorem optimize_const (o : BinOp) (h : o ≠ .sub) (X : WordLangExpHOL (BitVec 64)) (w : BitVec 64)
    (hX : WordInst.isConst X = false) :
    WordInst.ExecutablePullExp.optimizeNonSub o h [.const w, X] = WordInst.reduceConst o w [X] := by
  have hw : WordInst.isConst (.const w : WordLangExpHOL (BitVec 64)) = true := rfl
  simp only [WordInst.ExecutablePullExp.optimizeNonSub, holPartition, holPart, hX, hw, if_true,
    Bool.false_eq_true, if_false, List.map, WordInst.rmConst, nonSubWordOp_one]

theorem convertSub_two (X Y : WordLangExpHOL (BitVec 64)) :
    (∃ w, WordInst.convertSub [X, Y] = .const w) ∨
    (∃ w, Y = .const w ∧ WordInst.convertSub [X, Y] = .op .add [.const (-w), X]) ∨
    (WordInst.isConst Y = false ∧ WordInst.convertSub [X, Y] = .op .sub [X, Y]) := by
  cases X <;> cases Y <;> simp [WordInst.convertSub, WordInst.isConst]

theorem flat_const (w : BitVec 64) : WordInst.flattenExp (.const w) = .const w := by
  rw [WordInst.flattenExp.eq_def]
theorem flat_var (v : Nat) : WordInst.flattenExp (.var v : WordLangExpHOL (BitVec 64)) = .var v := by
  rw [WordInst.flattenExp.eq_def]
theorem flat_lookup (st : WordStoreHOL) : WordInst.flattenExp (.lookup st : WordLangExpHOL (BitVec 64)) = .lookup st := by
  rw [WordInst.flattenExp.eq_def]

open WordInst.ExecutablePullExp in
theorem pull_const (w : BitVec 64) : pullExpExecutable (.const w) = .const w := by
  rw [pullExpExecutable.eq_def]
open WordInst.ExecutablePullExp in
theorem pull_var (v : Nat) : pullExpExecutable (.var v : WordLangExpHOL (BitVec 64)) = .var v := by
  rw [pullExpExecutable.eq_def]
open WordInst.ExecutablePullExp in
theorem pull_lookup (st : WordStoreHOL) : pullExpExecutable (.lookup st : WordLangExpHOL (BitVec 64)) = .lookup st := by
  rw [pullExpExecutable.eq_def]

theorem selT_topAddr (ctxt : Spt Nat) : selT c (LoopToWord.compExpHOL ctxt .topAddr) = 72 := by
  rw [LoopToWord.compExpHOL]
  unfold selT
  rw [pull_op2 .add (by decide), pull_lookup, pull_shift, pull_lookup, pull_const,
    pullOps_two .add _ _ (by intro ls h; cases h) (by intro ls h; cases h),
    optimize_two .add (by decide) _ _ rfl rfl, flat_op2 .add (by decide), flat_shift, flat_lookup, flat_lookup, flat_const,
    iselT.eq_7 c .add _ _ (by intro w h; cases h), iselT_shift_const, iselT_lookup]
  simp [WordInst.isLookupCurrHeap]

end Shapes

/-- Operands whose pulled form is neither a constant nor an `op o` (no merge). -/
def safeL (o : BinOp) : HolLoopExp 64 → Bool
  | .var _ | .lookup _ | .baseAddr | .load _ | .shift .. => true
  | .topAddr => o != .add
  | _ => false

/-- Pattern-aware price of a Loop expression: at least its exact selected cost. -/
def fLT (c : Compiler.Encoders.Asm.AsmConfigExact 64) : HolLoopExp 64 → Nat
  | .const _ | .var _ | .lookup _ | .baseAddr => 24
  | .topAddr => 72
  | .load (.op .sub [a, .const w]) =>
      if WordInst.addrOffsetOk c (-w) then fLT c a + 24 else fLT c (.op .sub [a, .const w]) + 24
  | .load (.op .add [a, .const w]) =>
      if safeL .add a && WordInst.addrOffsetOk c w then fLT c a + 24 else fLT c (.op .add [a, .const w]) + 24
  | .load a => fLT c a + 24
  | .shift _ a (.const n) => if n.toNat < 64 then fLT c a + 24 else 24
  | .shift _ a b => fLT c a + fLT c b + 28
  | .op .sub [a, .const w] => fLT c a + immC c .add (-w)
  | .op .sub [a, b] => fLT c a + fLT c b + 24
  | .op o [a, .const w] => if safeL o a then fLT c a + immC c o w else fL (.op o [a, .const w])
  | .op o [a, b] => if safeL o a && safeL o b then fLT c a + fLT c b + 24 else fL (.op o [a, b])
  | e => fL e
termination_by e => sizeOf e


theorem immC_ge (c : Compiler.Encoders.Asm.AsmConfigExact 64) (o : BinOp) (w : BitVec 64) :
    24 ≤ immC c o w ∧ immC c o w ≤ 48 := by
  unfold immC; split_ifs <;> omega

theorem fL_ge (e : HolLoopExp 64) : 24 ≤ fL e := by
  rw [← fW_compExp .ln e]; exact fW_pos _

/-- Side conditions of the catch-all `fLT` equation for an operator of arity other than two. -/
theorem fLT_op_other (c : Compiler.Encoders.Asm.AsmConfigExact 64) (o : BinOp) (ls : List (HolLoopExp 64))
    (h : ls.length ≠ 2) : fLT c (.op o ls) = fL (.op o ls) := by
  rw [fLT.eq_15] <;> intros <;> simp_all

theorem fLT_ge (c : Compiler.Encoders.Asm.AsmConfigExact 64) (e : HolLoopExp 64) : 24 ≤ fLT c e := by
  refine (measure (sizeOf : HolLoopExp 64 → Nat)).wf.induction (C := fun e => 24 ≤ fLT c e) e ?_
  intro e ih
  cases e with
  | const w => rw [fLT.eq_1]
  | var v => rw [fLT.eq_2]
  | lookup a => rw [fLT.eq_3]
  | baseAddr => rw [fLT.eq_4]
  | topAddr => rw [fLT.eq_5]; omega
  | load x =>
    by_cases hs : ∃ a w, x = .op .sub [a, .const w]
    · obtain ⟨a, w, rfl⟩ := hs
      rw [fLT.eq_6]; split_ifs <;> omega
    · by_cases hd : ∃ a w, x = .op .add [a, .const w]
      · obtain ⟨a, w, rfl⟩ := hd
        rw [fLT.eq_7]; split_ifs <;> omega
      · rw [fLT.eq_8 c x (fun a w h => hs ⟨a, w, h⟩) (fun a w h => hd ⟨a, w, h⟩)]; omega
  | shift s a b =>
    by_cases hb : ∃ n, b = .const n
    · obtain ⟨n, rfl⟩ := hb
      rw [fLT.eq_9]; split_ifs <;> omega
    · rw [fLT.eq_10 c s a b (fun n h => hb ⟨n, h⟩)]; omega
  | op o ls =>
    rcases ls with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
    · rw [fLT_op_other c o [] (by simp)]; exact fL_ge _
    · rw [fLT_op_other c o [a] (by simp)]; exact fL_ge _
    · have ha := ih a (by show sizeOf a < _; simp; omega)
      have := immC_ge c o
      by_cases ho : o = .sub
      · subst ho
        by_cases hb : ∃ w, b = .const w
        · obtain ⟨w, rfl⟩ := hb
          rw [fLT.eq_11]; have := immC_ge c .add (-w); omega
        · rw [fLT.eq_12 c a b (fun w h => hb ⟨w, h⟩)]; omega
      · by_cases hb : ∃ w, b = .const w
        · obtain ⟨w, rfl⟩ := hb
          rw [fLT.eq_13 c o a w ho]; have := immC_ge c o w; split_ifs
          · omega
          · exact fL_ge _
        · rw [fLT.eq_14 c o a b (fun w _ h => hb ⟨w, h⟩) ho (fun w h => hb ⟨w, h⟩)]; split_ifs
          · omega
          · exact fL_ge _
    · rw [fLT_op_other c o _ (by simp)]; exact fL_ge _

/-- A safe operand pulls to a non-constant expression that is not an `op o`. -/
theorem safe_shape (ctxt : Spt Nat) (o : BinOp) (a : HolLoopExp 64) (hs : safeL o a = true) :
    WordInst.isConst (WordInst.ExecutablePullExp.pullExpExecutable (LoopToWord.compExpHOL ctxt a)) = false ∧
    ∀ ls, WordInst.ExecutablePullExp.pullExpExecutable (LoopToWord.compExpHOL ctxt a) ≠ .op o ls := by
  cases a with
  | var v => rw [LoopToWord.compExpHOL, pull_var]; exact ⟨rfl, fun _ h => by cases h⟩
  | lookup x => rw [LoopToWord.compExpHOL, pull_lookup]; exact ⟨rfl, fun _ h => by cases h⟩
  | baseAddr => rw [LoopToWord.compExpHOL, pull_lookup]; exact ⟨rfl, fun _ h => by cases h⟩
  | load x => rw [LoopToWord.compExpHOL, pull_load]; exact ⟨rfl, fun _ h => by cases h⟩
  | shift s x y => rw [LoopToWord.compExpHOL, pull_shift]; exact ⟨rfl, fun _ h => by cases h⟩
  | topAddr =>
    simp only [safeL, bne_iff_ne, ne_eq] at hs
    rw [LoopToWord.compExpHOL, pull_op2 .add (by decide), pull_lookup, pull_shift, pull_lookup, pull_const,
      pullOps_two .add _ _ (by intro ls h; cases h) (by intro ls h; cases h),
      optimize_two .add (by decide) _ _ rfl rfl]
    refine ⟨rfl, fun ls h => ?_⟩
    cases h; exact hs rfl
  | _ => simp [safeL] at hs


section Main
variable (c : Compiler.Encoders.Asm.AsmConfigExact 64) (ctxt : Spt Nat)

local notation "PL" e => WordInst.ExecutablePullExp.pullExpExecutable (LoopToWord.compExpHOL ctxt e)
local notation "NL" e => WordInst.flattenExp (WordInst.ExecutablePullExp.pullExpExecutable (LoopToWord.compExpHOL ctxt e))

theorem comp_op2 (o : BinOp) (a b : HolLoopExp 64) :
    LoopToWord.compExpHOL ctxt (.op o [a, b]) = .op o [LoopToWord.compExpHOL ctxt a, LoopToWord.compExpHOL ctxt b] := by
  rw [LoopToWord.compExpHOL]; simp

theorem comp_const (w : BitVec 64) : LoopToWord.compExpHOL ctxt (.const w) = .const w := by
  rw [LoopToWord.compExpHOL]

/-- `sub` with a constant right operand after `convert_sub` and `flatten_exp`. -/
theorem subc_cases (a : HolLoopExp 64) (w : BitVec 64) :
    (∃ w', (NL (.op .sub [a, .const w])) = .const w') ∨
    (NL (.op .sub [a, .const w])) = .op .add [NL a, .const (-w)] := by
  rw [comp_op2, comp_const, pull_sub2, pull_const]
  rcases convertSub_two (PL a) (.const w) with ⟨w', h⟩ | ⟨w', hw, h⟩ | ⟨h, _⟩
  · exact Or.inl ⟨w', by rw [h, flat_const]⟩
  · cases hw; right; rw [h, flat_op2 .add (by decide), flat_const]
  · simp [WordInst.isConst] at h

theorem selT_le_fLT (e : HolLoopExp 64) : selT c (LoopToWord.compExpHOL ctxt e) ≤ fLT c e := by
  refine (measure (sizeOf : HolLoopExp 64 → Nat)).wf.induction (C := fun e =>
    selT c (LoopToWord.compExpHOL ctxt e) ≤ fLT c e) e ?_
  intro e ih
  unfold selT at ih ⊢
  cases e with
  | const w => rw [comp_const, pull_const, flat_const, iselT_const, fLT.eq_1]
  | var v => rw [LoopToWord.compExpHOL, pull_var, flat_var, iselT_var, fLT.eq_2]
  | lookup x => rw [LoopToWord.compExpHOL, pull_lookup, flat_lookup, iselT_lookup, fLT.eq_3]
  | baseAddr => rw [LoopToWord.compExpHOL, pull_lookup, flat_lookup, iselT_lookup, fLT.eq_4]
  | topAddr => have := selT_topAddr c ctxt; unfold selT at this; rw [this, fLT.eq_5]
  | load x =>
    by_cases hs : ∃ a w, x = .op .sub [a, .const w]
    · obtain ⟨a, w, rfl⟩ := hs
      have ha := ih a (by show sizeOf a < _; simp; omega)
      have hsub := ih (.op .sub [a, .const w]) (by show sizeOf _ < _; simp)
      have ga := fLT_ge c a
      have gi := immC_ge c .add (-w)
      rw [fLT.eq_11] at hsub
      rw [LoopToWord.compExpHOL, pull_load, flat_load, fLT.eq_6, fLT.eq_11]
      rcases subc_cases ctxt a w with ⟨w', h⟩ | h
      · rw [h, iselT.eq_2 c _ (fun _ _ h => by cases h), iselT_const]
        split_ifs <;> omega
      · rw [h]
        split_ifs with hok
        · rw [iselT_load_offset c _ _ hok]; omega
        · have := iselT_load_le c (.op .add [NL a, .const (-w)])
          have := iselT_op_const c .add (NL a) (-w)
          omega
    · have hx := ih x (by show sizeOf x < _; simp)
      by_cases hd : ∃ a w, x = .op .add [a, .const w]
      · obtain ⟨a, w, rfl⟩ := hd
        have ha := ih a (by show sizeOf a < _; simp; omega)
        rw [LoopToWord.compExpHOL, pull_load, flat_load, fLT.eq_7]
        split_ifs with hcond
        · simp only [Bool.and_eq_true] at hcond
          obtain ⟨hsafe, hok⟩ := hcond
          obtain ⟨hc, hno⟩ := safe_shape ctxt .add a hsafe
          rw [comp_op2, comp_const, pull_op2 .add (by decide), pull_const,
            pullOps_two .add _ _ hno (by intro ls h; cases h), optimize_const .add (by decide) _ w hc]
          unfold WordInst.reduceConst
          split_ifs
          · simp only []
            have := iselT_load_le c (NL a); omega
          all_goals first
            | (rw [flat_op2 .add (by decide), flat_const, iselT_load_offset c _ _ hok]; omega)
            | (exfalso; simp_all)
        · have := iselT_load_le c (NL (.op .add [a, .const w])); omega
      · rw [LoopToWord.compExpHOL, pull_load, flat_load,
          fLT.eq_8 c x (fun a w h => hs ⟨a, w, h⟩) (fun a w h => hd ⟨a, w, h⟩)]
        have := iselT_load_le c (NL x); omega
  | shift s a b =>
    have ha := ih a (by show sizeOf a < _; simp; omega)
    rw [LoopToWord.compExpHOL, pull_shift, flat_shift]
    by_cases hb : ∃ n, b = .const n
    · obtain ⟨n, rfl⟩ := hb
      rw [comp_const, pull_const, flat_const, iselT_shift_const, fLT.eq_9]
      split_ifs <;> omega
    · have hb' := ih b (by show sizeOf b < _; simp)
      rw [fLT.eq_10 c s a b (fun n h => hb ⟨n, h⟩)]
      have := iselT_shift_le c s (NL a) (NL b); omega
  | op o ls =>
    rcases ls with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
    · rw [fLT_op_other c o [] (by simp)]; exact selT_le_fL c ctxt _
    · rw [fLT_op_other c o [a] (by simp)]; exact selT_le_fL c ctxt _
    · have ha := ih a (by show sizeOf a < _; simp; omega)
      have ga := fLT_ge c a
      by_cases ho : o = .sub
      · subst ho
        by_cases hb : ∃ w, b = .const w
        · obtain ⟨w, rfl⟩ := hb
          have gi := immC_ge c .add (-w)
          rw [fLT.eq_11]
          rcases subc_cases ctxt a w with ⟨w', h⟩ | h
          · rw [h, iselT_const]; omega
          · rw [h]; have := iselT_op_const c .add (NL a) (-w); omega
        · have hbb := ih b (by show sizeOf b < _; simp; omega)
          have gb := fLT_ge c b
          rw [fLT.eq_12 c a b (fun w h => hb ⟨w, h⟩), comp_op2, pull_sub2]
          rcases convertSub_two (PL a) (PL b) with ⟨w', h⟩ | ⟨w', hw, h⟩ | ⟨_, h⟩
          · rw [h, flat_const, iselT_const]; omega
          · rw [h, flat_op2 .add (by decide), flat_const]
            have := iselT_op_const c .add (NL a) (-w')
            have := immC_ge c .add (-w'); omega
          · rw [h, flat_sub2]
            have := iselT_op_le c .sub (NL a) (NL b); omega
      · by_cases hb : ∃ w, b = .const w
        · obtain ⟨w, rfl⟩ := hb
          rw [fLT.eq_13 c o a w ho]
          split_ifs with hs
          · obtain ⟨hc, hno⟩ := safe_shape ctxt o a hs
            have gi := immC_ge c o w
            rw [comp_op2, comp_const, pull_op2 o ho, pull_const,
              pullOps_two o _ _ (hno) (by intro ls h; cases h), optimize_const o ho _ w hc]
            unfold WordInst.reduceConst
            split_ifs
            · split
              · rw [flat_const, iselT_const]; omega
              · rename_i x hx; cases hx; omega
              · rename_i hx; exact absurd rfl (hx _)
            · rw [flat_const, iselT_const]; omega
            · rw [flat_op2 o ho, flat_const]; have := iselT_op_const c o (NL a) w; omega
            · rw [flat_op2 o ho, flat_const]; have := iselT_op_const c o (NL a) w; omega
          · exact selT_le_fL c ctxt _
        · rw [fLT.eq_14 c o a b (fun w _ h => hb ⟨w, h⟩) ho (fun w h => hb ⟨w, h⟩)]
          split_ifs with hs
          · simp only [Bool.and_eq_true] at hs
            have hbb := ih b (by show sizeOf b < _; simp; omega)
            obtain ⟨hca, hna⟩ := safe_shape ctxt o a hs.1
            obtain ⟨hcb, hnb⟩ := safe_shape ctxt o b hs.2
            rw [comp_op2, pull_op2 o ho, pullOps_two o _ _ hna hnb, optimize_two o ho _ _ hca hcb,
              flat_op2 o ho]
            have := iselT_op_le c o (NL b) (NL a); omega
          · exact selT_le_fL c ctxt _
    · rw [fLT_op_other c o _ (by simp)]; exact selT_le_fL c ctxt _

end Main


#print axioms iselT_op_le
#print axioms iselT_load_le
#print axioms pull_op2
#print axioms flat_op2
#print axioms iselT_le_iselCost
#print axioms selT_le_fL
#print axioms selT_topAddr
#print axioms fLT_ge
#print axioms safe_shape
#print axioms selT_le_fLT
end InitECandidate.Runtime.FineCost
