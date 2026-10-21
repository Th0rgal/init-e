import InitECandidate.Runtime.LoopSelTight
import InitECandidate.Runtime.CrepLoopPricingG
import InitECandidate.Runtime.CrepSelPrice
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend

/-! Pattern-aware selector prices of compiled Crep expressions. Expression
code is priced by `tightCodeWork` (an assignment pays `fLT` of its value),
and a Crep expression by `nodeT`: its code plus the `fLT` price of its Loop
value. Shapes outside the patterns fall back to `selNodePrice`. -/

section Code
variable (c : Compiler.Encoders.Asm.AsmConfigExact 64)

theorem leafPL_assignT (n : Nat) (v : HolLoopExp 64) :
    ∃ k, leafPL c wsT1 wsT2 (.assign n v) = some k ∧ k ≤ fLT c v := by
  refine ⟨iselX c (.assign (LoopToWord.findVarHOL .ln n) (LoopToWord.compExpHOL .ln v)), ?_, ?_⟩
  · simp [leafPL, loopWorkLeafCost, LoopToWord.compHOL, lineBound, isLeafProg, leafNodeB, isExprStmt, nodeEnv,
      siteKey]
  · obtain ⟨k, hk, hle⟩ := isel_assign_lineBoundT c 0 (LoopToWord.findVarHOL .ln n) (LoopToWord.compExpHOL .ln v)
    have := selT_le_fLT c .ln v
    simp only [iselX, hk, Option.getD_some]
    omega

/-- Tight allowance of expression-generated Loop code. -/
def tightCodeWork : HolLoopProg 64 → Option Nat
  | .skip => some 0
  | .assign _ v => some (fLT c v)
  | .arith _ => some 27
  | .load32 _ _ | .loadByte _ _ => some 24
  | .seq a b => do
      let x ← tightCodeWork a
      let y ← tightCodeWork b
      pure (x + y)
  | .ite _ _ _ y n _ => do
      let a ← tightCodeWork y
      let b ← tightCodeWork n
      pure (37 + max a b)
  | _ => none

theorem tightCodeWork_bounded :
    ∀ (p : HolLoopProg 64) (k : Nat), tightCodeWork c p = some k → LoopBoundedS c p k
  | .skip, k, h => by
    simp only [tightCodeWork, Option.some.injEq] at h; subst h
    exact selCodeWork_bounded c .skip 0 rfl
  | .assign n v, k, h => by
    simp only [tightCodeWork, Option.some.injEq] at h; subst h
    obtain ⟨k', hk, hle⟩ := leafPL_assignT c n v
    exact loopBoundedS_leaf hk hle
  | .arith op, k, h => by
    simp only [tightCodeWork, Option.some.injEq] at h; subst h
    exact selCodeWork_bounded c (.arith op) 27 rfl
  | .load32 a d, k, h => by
    simp only [tightCodeWork, Option.some.injEq] at h; subst h
    exact selCodeWork_bounded c (.load32 a d) 24 rfl
  | .loadByte a d, k, h => by
    simp only [tightCodeWork, Option.some.injEq] at h; subst h
    exact selCodeWork_bounded c (.loadByte a d) 24 rfl
  | .seq a b, k, h => by
    simp only [tightCodeWork] at h
    rcases ha : tightCodeWork c a with _ | x <;> rcases hb : tightCodeWork c b with _ | y <;> simp [ha, hb] at h
    subst h
    exact loopBoundedS_seq (tightCodeWork_bounded a x ha) (tightCodeWork_bounded b y hb)
  | .ite op r ri yes no live, k, h => by
    simp only [tightCodeWork] at h
    rcases ha : tightCodeWork c yes with _ | x <;> rcases hb : tightCodeWork c no with _ | y <;> simp [ha, hb] at h
    subst h
    exact loopBoundedS_ite (tightCodeWork_bounded yes x ha) (tightCodeWork_bounded no y hb)
  | .loop _ _ _, k, h | .mark _, k, h | .call _ _ _ _, k, h | .primitive _ _ _, k, h | .store _ _, k, h
  | .setGlobal _ _, k, h | .store32 _ _, k, h | .storeByte _ _, k, h | .break _, k, h | .continue _, k, h
  | .raise _, k, h | .return _, k, h | .shMem _ _ _, k, h | .tick, k, h | .fail, k, h | .locValue _ _, k, h
  | .ffi _ _ _ _ _ _, k, h => by simp [tightCodeWork] at h

/-- The tight allowance at the selector-derived leaf price. -/
noncomputable def tightAllowance : CodeAllowance (wsLeaf c) where
  work := tightCodeWork c
  sound := fun p k h F f s => tightCodeWork_bounded c p k h F f s

/-- The pattern-aware Loop price never exceeds the structural one. -/
theorem fLT_le_fL (e : HolLoopExp 64) : fLT c e ≤ fL e := by
  refine (measure (sizeOf : HolLoopExp 64 → Nat)).wf.induction (C := fun e => fLT c e ≤ fL e) e ?_
  intro e ih
  cases e with
  | const w => rw [fLT.eq_1]; simp [fL]
  | var v => rw [fLT.eq_2]; simp [fL]
  | lookup a => rw [fLT.eq_3]; simp [fL]
  | baseAddr => rw [fLT.eq_4]; simp [fL]
  | topAddr => rw [fLT.eq_5]; simp [fL, fLs]
  | load x =>
    have hx := ih x (by show sizeOf x < _; simp)
    by_cases hs : ∃ a w, x = .op .sub [a, .const w]
    · obtain ⟨a, w, rfl⟩ := hs
      have ha := ih a (by show sizeOf a < _; simp; omega)
      have := immC_ge c .add (-w)
      rw [fLT.eq_6, fLT.eq_11]; rw [fLT.eq_11] at hx
      simp only [fL, fLs] at hx ⊢
      split_ifs <;> simp at hx ⊢ <;> omega
    · by_cases hd : ∃ a w, x = .op .add [a, .const w]
      · obtain ⟨a, w, rfl⟩ := hd
        have ha := ih a (by show sizeOf a < _; simp; omega)
        rw [fLT.eq_7]
        simp only [fL, fLs] at hx ⊢
        split_ifs <;> simp at hx ⊢ <;> omega
      · rw [fLT.eq_8 c x (fun a w h => hs ⟨a, w, h⟩) (fun a w h => hd ⟨a, w, h⟩)]; simp only [fL]; omega
  | shift s a b =>
    have ha := ih a (by show sizeOf a < _; simp; omega)
    by_cases hb : ∃ n, b = .const n
    · obtain ⟨n, rfl⟩ := hb
      rw [fLT.eq_9]; simp only [fL]; split_ifs <;> omega
    · have hb' := ih b (by show sizeOf b < _; simp)
      rw [fLT.eq_10 c s a b (fun n h => hb ⟨n, h⟩)]; simp only [fL]; omega
  | op o ls =>
    rcases ls with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
    · rw [fLT_op_other c o [] (by simp)]
    · rw [fLT_op_other c o [a] (by simp)]
    · have ha := ih a (by show sizeOf a < _; simp; omega)
      by_cases ho : o = .sub
      · subst ho
        by_cases hb : ∃ w, b = .const w
        · obtain ⟨w, rfl⟩ := hb
          have := immC_ge c .add (-w)
          rw [fLT.eq_11]; simp [fL, fLs]; omega
        · have hbb := ih b (by show sizeOf b < _; simp; omega)
          rw [fLT.eq_12 c a b (fun w h => hb ⟨w, h⟩)]; simp [fL, fLs]; omega
      · by_cases hb : ∃ w, b = .const w
        · obtain ⟨w, rfl⟩ := hb
          have := immC_ge c o w
          rw [fLT.eq_13 c o a w ho]; split_ifs
          · simp [fL, fLs]; omega
          · exact Nat.le_refl _
        · have hbb := ih b (by show sizeOf b < _; simp; omega)
          rw [fLT.eq_14 c o a b (fun w _ h => hb ⟨w, h⟩) ho (fun w h => hb ⟨w, h⟩)]; split_ifs
          · simp [fL, fLs]; omega
          · exact Nat.le_refl _
    · rw [fLT_op_other c o _ (by simp)]

theorem tightCodeWork_le : ∀ (p : HolLoopProg 64) (k : Nat), selCodeWork p = some k →
    ∃ k', tightCodeWork c p = some k' ∧ k' ≤ k
  | .skip, k, h => ⟨0, rfl, by simp [selCodeWork] at h; omega⟩
  | .assign n v, k, h => by
    simp only [selCodeWork, Option.some.injEq] at h; subst h
    exact ⟨_, rfl, fLT_le_fL c v⟩
  | .arith op, k, h => by simp only [selCodeWork, Option.some.injEq] at h; subst h; exact ⟨_, rfl, Nat.le_refl _⟩
  | .load32 a d, k, h => by simp only [selCodeWork, Option.some.injEq] at h; subst h; exact ⟨_, rfl, Nat.le_refl _⟩
  | .loadByte a d, k, h => by simp only [selCodeWork, Option.some.injEq] at h; subst h; exact ⟨_, rfl, Nat.le_refl _⟩
  | .seq a b, k, h => by
    simp only [selCodeWork] at h
    rcases ha : selCodeWork a with _ | x <;> rcases hb : selCodeWork b with _ | y <;> simp [ha, hb] at h
    subst h
    obtain ⟨x', hx, lx⟩ := tightCodeWork_le a x ha
    obtain ⟨y', hy, ly⟩ := tightCodeWork_le b y hb
    exact ⟨x' + y', by simp [tightCodeWork, hx, hy], by omega⟩
  | .ite op r ri yes no live, k, h => by
    simp only [selCodeWork] at h
    rcases ha : selCodeWork yes with _ | x <;> rcases hb : selCodeWork no with _ | y <;> simp [ha, hb] at h
    subst h
    obtain ⟨x', hx, lx⟩ := tightCodeWork_le yes x ha
    obtain ⟨y', hy, ly⟩ := tightCodeWork_le no y hb
    exact ⟨37 + max x' y', by simp [tightCodeWork, hx, hy], by omega⟩
  | .loop _ _ _, k, h | .mark _, k, h | .call _ _ _ _, k, h | .primitive _ _ _, k, h | .store _ _, k, h
  | .setGlobal _ _, k, h | .store32 _ _, k, h | .storeByte _ _, k, h | .break _, k, h | .continue _, k, h
  | .raise _, k, h | .return _, k, h | .shMem _ _ _, k, h | .tick, k, h | .fail, k, h | .locValue _ _, k, h
  | .ffi _ _ _ _ _ _, k, h => by simp [selCodeWork] at h

theorem tightWorks_le : ∀ (codes : List (HolLoopProg 64)) (k : Nat), selCodesWork codes = some k →
    ∃ k', (tightAllowance c).works codes = some k' ∧ k' ≤ k
  | [], k, h => ⟨0, rfl, by simp [selCodesWork] at h; omega⟩
  | p :: ps, k, h => by
    simp only [selCodesWork] at h
    rcases ha : selCodeWork p with _ | x <;> rcases hb : selCodesWork ps with _ | y <;> simp [ha, hb] at h
    subst h
    obtain ⟨x', hx, lx⟩ := tightCodeWork_le c p x ha
    obtain ⟨y', hy, ly⟩ := tightWorks_le ps y hb
    refine ⟨x' + y', ?_, by omega⟩
    simp only [CodeAllowance.works, hy]
    show (tightCodeWork c p >>= fun a => some (a + y')) = _
    rw [hx]; rfl

end Code

/-- Crep operands whose compiled Loop value is safe for `op o` (`safeL`). -/
def safeC (o : BinOp) : CrepExpHOL 64 → Bool
  | .var _ | .loadGlob _ | .baseAddr | .load _ | .load32 _ | .loadByte _ | .shift .. | .crepOp .. | .cmp .. => true
  | .topAddr => o != .add
  | _ => false

/-- Pattern-aware selector price of a Crep expression. -/
def nodeT (c : Compiler.Encoders.Asm.AsmConfigExact 64) : CrepExpHOL 64 → Nat
  | .const _ | .var _ | .loadGlob _ | .baseAddr => 24
  | .topAddr => 72
  | .load (.op .sub [a, .const w]) =>
      if WordInst.addrOffsetOk c (-w) then nodeT c a + 24 else nodeT c (.op .sub [a, .const w]) + 24
  | .load (.op .add [a, .const w]) =>
      if safeC .add a && WordInst.addrOffsetOk c w then nodeT c a + 24 else nodeT c (.op .add [a, .const w]) + 24
  | .load a => nodeT c a + 24
  | .load32 a | .loadByte a => nodeT c a + 48
  | .shift _ a (.const _) => nodeT c a + 24
  | .shift _ a b => nodeT c a + nodeT c b + 28
  | .op .sub [a, .const w] => nodeT c a + immC c .add (-w)
  | .op .sub [a, b] => nodeT c a + nodeT c b + 24
  | .op o [a, .const w] => if safeC o a then nodeT c a + immC c o w else selNodePrice (.op o [a, .const w])
  | .op o [a, b] => if safeC o a && safeC o b then nodeT c a + nodeT c b + 24 else selNodePrice (.op o [a, b])
  | e => selNodePrice e
termination_by e => sizeOf e


section Crep
variable (c : Compiler.Encoders.Asm.AsmConfigExact 64) (ctxt : CrepToLoopContextExact)

theorem tightWorks_append : ∀ (l r : List (HolLoopProg 64)),
    (tightAllowance c).works (l ++ r) = (do
      let a ← (tightAllowance c).works l
      let b ← (tightAllowance c).works r
      pure (a + b))
  | [], r => by simp [CodeAllowance.works]
  | p :: l, r => by
    simp only [List.cons_append, CodeAllowance.works, tightWorks_append l r]
    cases (tightAllowance c).work p <;> cases (tightAllowance c).works l <;> cases (tightAllowance c).works r <;>
      simp [Nat.add_assoc]

theorem comp_two (tmp : Nat) (live : NumSet) (a b : CrepExpHOL 64) :
    compileExpsHOLExact ctxt tmp live [a, b] =
      ((compileExpHOLExact ctxt tmp live a).1 ++
        (compileExpHOLExact ctxt (compileExpHOLExact ctxt tmp live a).2.2.1
          (compileExpHOLExact ctxt tmp live a).2.2.2 b).1,
       [(compileExpHOLExact ctxt tmp live a).2.1,
        (compileExpHOLExact ctxt (compileExpHOLExact ctxt tmp live a).2.2.1
          (compileExpHOLExact ctxt tmp live a).2.2.2 b).2.1],
       (compileExpHOLExact ctxt (compileExpHOLExact ctxt tmp live a).2.2.1
          (compileExpHOLExact ctxt tmp live a).2.2.2 b).2.2.1,
       (compileExpHOLExact ctxt (compileExpHOLExact ctxt tmp live a).2.2.1
          (compileExpHOLExact ctxt tmp live a).2.2.2 b).2.2.2) := by
  rcases ha : compileExpHOLExact ctxt tmp live a with ⟨ca, va, na, la⟩
  rcases hb : compileExpHOLExact ctxt na la b with ⟨cb, vb, nb, lb⟩
  simp [compileExpsHOLExact, ha, hb]

theorem comp_value_nonconst (tmp : Nat) (live : NumSet) (e : CrepExpHOL 64) (h : ∀ w, e ≠ .const w) :
    ∀ w, (compileExpHOLExact ctxt tmp live e).2.1 ≠ .const w := by
  intro w hw
  cases e with
  | const v => exact h v rfl
  | load x =>
    rw [compileExpHOLExact] at hw
    rcases compileExpHOLExact ctxt tmp live x with ⟨_, _, _, _⟩; simp at hw
  | load32 x =>
    rw [compileExpHOLExact] at hw
    rcases compileExpHOLExact ctxt tmp live x with ⟨_, _, _, _⟩; simp at hw
  | loadByte x =>
    rw [compileExpHOLExact] at hw
    rcases compileExpHOLExact ctxt tmp live x with ⟨_, _, _, _⟩; simp at hw
  | op o xs =>
    rw [compileExpHOLExact] at hw
    rcases compileExpsHOLExact ctxt tmp live xs with ⟨_, _, _, _⟩; simp at hw
  | crepOp o xs =>
    rw [compileExpHOLExact] at hw
    rcases compileExpsHOLExact ctxt tmp live xs with ⟨_, _, _, _⟩; simp at hw
  | cmp o x y =>
    rw [compileExpHOLExact] at hw
    rcases compileExpHOLExact ctxt tmp live x with ⟨_, _, n1, l1⟩
    rcases compileExpHOLExact ctxt n1 l1 y with ⟨_, _, _, _⟩; simp at hw
  | shift o x y =>
    rw [compileExpHOLExact] at hw
    rcases compileExpHOLExact ctxt tmp live x with ⟨_, _, n1, l1⟩
    rcases compileExpHOLExact ctxt n1 l1 y with ⟨_, _, _, _⟩; simp at hw
  | _ => simp [compileExpHOLExact] at hw

theorem comp_value_safe (tmp : Nat) (live : NumSet) (o : BinOp) (e : CrepExpHOL 64) (h : safeC o e = true) :
    safeL o (compileExpHOLExact ctxt tmp live e).2.1 = true := by
  cases e with
  | load x =>
    rw [compileExpHOLExact]; rcases compileExpHOLExact ctxt tmp live x with ⟨_, _, _, _⟩; rfl
  | load32 x =>
    rw [compileExpHOLExact]; rcases compileExpHOLExact ctxt tmp live x with ⟨_, _, _, _⟩; rfl
  | loadByte x =>
    rw [compileExpHOLExact]; rcases compileExpHOLExact ctxt tmp live x with ⟨_, _, _, _⟩; rfl
  | crepOp o' xs =>
    rw [compileExpHOLExact]; rcases compileExpsHOLExact ctxt tmp live xs with ⟨_, vs, n, l⟩
    simp only []; rcases compileCrepopHOLExact o' ctxt.target n (n + 1) (n + vs.length) _ with ⟨_, _⟩; rfl
  | cmp o' x y =>
    rw [compileExpHOLExact]
    rcases compileExpHOLExact ctxt tmp live x with ⟨_, _, n1, l1⟩
    rcases compileExpHOLExact ctxt n1 l1 y with ⟨_, _, _, _⟩; rfl
  | shift o' x y =>
    rw [compileExpHOLExact]
    rcases compileExpHOLExact ctxt tmp live x with ⟨_, _, n1, l1⟩
    rcases compileExpHOLExact ctxt n1 l1 y with ⟨_, _, _, _⟩; rfl
  | var v => simp [compileExpHOLExact, safeL]
  | loadGlob a => simp [compileExpHOLExact, safeL]
  | baseAddr => simp [compileExpHOLExact, safeL]
  | topAddr => simpa [compileExpHOLExact, safeL, safeC] using h
  | _ => simp [safeC] at h

theorem fLT_load_le (v : HolLoopExp 64) : fLT c (.load v) ≤ fLT c v + 24 := by
  by_cases hs : ∃ a w, v = .op .sub [a, .const w]
  · obtain ⟨a, w, rfl⟩ := hs
    rw [fLT.eq_6, fLT.eq_11]; split_ifs <;> omega
  · by_cases hd : ∃ a w, v = .op .add [a, .const w]
    · obtain ⟨a, w, rfl⟩ := hd
      have h1 : fLT c a ≤ fLT c (.op .add [a, .const w]) := by
        rw [fLT.eq_13 c .add a w (by decide)]
        split_ifs
        · omega
        · have := fLT_le_fL c a; simp [fL, fLs]; omega
      rw [fLT.eq_7]; split_ifs <;> omega
    · rw [fLT.eq_8 c v (fun a w h => hs ⟨a, w, h⟩) (fun a w h => hd ⟨a, w, h⟩)]

theorem tight_fallback (tmp : Nat) (live : NumSet) (e : CrepExpHOL 64) :
    ∃ cost, (tightAllowance c).works (compileExpHOLExact ctxt tmp live e).1 = some cost ∧
      cost + fLT c (compileExpHOLExact ctxt tmp live e).2.1 ≤ selNodePrice e := by
  obtain ⟨k, hk, hb⟩ := crep_to_loop_sel_work ctxt tmp live e
  obtain ⟨k', hk', hle⟩ := tightWorks_le c _ k hk
  have := fLT_le_fL c (compileExpHOLExact ctxt tmp live e).2.1
  exact ⟨k', hk', by omega⟩

theorem tightWorks_nil : (tightAllowance c).works [] = some 0 := rfl

/-- Compiled Crep expression code and value are within the pattern-aware price. -/
theorem crep_to_loop_T_work (e : CrepExpHOL 64) : ∀ (tmp : Nat) (live : NumSet),
    ∃ cost, (tightAllowance c).works (compileExpHOLExact ctxt tmp live e).1 = some cost ∧
      cost + fLT c (compileExpHOLExact ctxt tmp live e).2.1 ≤ nodeT c e := by
  refine (measure (sizeOf : CrepExpHOL 64 → Nat)).wf.induction (C := fun e => ∀ (tmp : Nat) (live : NumSet),
    ∃ cost, (tightAllowance c).works (compileExpHOLExact ctxt tmp live e).1 = some cost ∧
      cost + fLT c (compileExpHOLExact ctxt tmp live e).2.1 ≤ nodeT c e) e ?_
  intro e ih tmp live
  cases e with
  | const v => exact ⟨0, by simp [compileExpHOLExact, tightWorks_nil], by simp [compileExpHOLExact, fLT.eq_1, nodeT.eq_1]⟩
  | var v => exact ⟨0, by simp [compileExpHOLExact, tightWorks_nil], by simp [compileExpHOLExact, fLT.eq_2, nodeT.eq_2]⟩
  | loadGlob a => exact ⟨0, by simp [compileExpHOLExact, tightWorks_nil], by simp [compileExpHOLExact, fLT.eq_3, nodeT.eq_3]⟩
  | baseAddr => exact ⟨0, by simp [compileExpHOLExact, tightWorks_nil], by simp [compileExpHOLExact, fLT.eq_4, nodeT.eq_4]⟩
  | topAddr => exact ⟨0, by simp [compileExpHOLExact, tightWorks_nil], by simp [compileExpHOLExact, fLT.eq_5, nodeT.eq_5]⟩
  | load x =>
    have hx := ih x (by show sizeOf x < _; simp) tmp live
    by_cases hs : ∃ a w, x = .op .sub [a, .const w]
    · obtain ⟨a, w, rfl⟩ := hs
      obtain ⟨ka, hka, hba⟩ := ih a (by show sizeOf a < _; simp; omega) tmp live
      rw [nodeT.eq_6, nodeT.eq_13]
      simp only [compileExpHOLExact, comp_two] at hka hba ⊢
      rcases hc : compileExpHOLExact ctxt tmp live a with ⟨ca, va, na, la⟩
      rw [hc] at hka hba
      try simp only [] at hka hba ⊢
      refine ⟨ka, by simpa [compileExpHOLExact] using hka, ?_⟩
      rw [fLT.eq_6, fLT.eq_11]
      split_ifs <;> omega
    · by_cases hd : ∃ a w, x = .op .add [a, .const w]
      · obtain ⟨a, w, rfl⟩ := hd
        obtain ⟨k, hk, hb⟩ := hx
        rw [nodeT.eq_7]
        split_ifs with hcond
        · simp only [Bool.and_eq_true] at hcond
          obtain ⟨hsafe, hok⟩ := hcond
          obtain ⟨ka, hka, hba⟩ := ih a (by show sizeOf a < _; simp; omega) tmp live
          have hsv := comp_value_safe ctxt tmp live .add a hsafe
          rcases hc : compileExpHOLExact ctxt tmp live a with ⟨ca, va, na, la⟩
          rw [hc] at hka hba hsv
          try simp only [] at hka hba hsv
          refine ⟨ka, by simpa [compileExpHOLExact, comp_two, hc] using hka, ?_⟩
          simp only [compileExpHOLExact, comp_two, hc]
          rw [fLT.eq_7, if_pos (by simp [hsv, hok])]; omega
        · rcases hc : compileExpHOLExact ctxt tmp live (.op .add [a, .const w]) with ⟨cx, vx, nx, lx⟩
          rw [hc] at hk hb
          try simp only [] at hk hb
          refine ⟨k, by rw [compileExpHOLExact, hc]; exact hk, ?_⟩
          rw [compileExpHOLExact, hc]
          simp only []
          have := fLT_load_le c vx; omega
      obtain ⟨k, hk, hb⟩ := hx
      rw [nodeT.eq_8 c x (fun a w h => hs ⟨a, w, h⟩) (fun a w h => hd ⟨a, w, h⟩)]
      rcases hc : compileExpHOLExact ctxt tmp live x with ⟨cx, vx, nx, lx⟩
      rw [hc] at hk hb
      simp only [] at hk hb
      refine ⟨k, by simpa [compileExpHOLExact, hc] using hk, ?_⟩
      simp only [compileExpHOLExact, hc]
      have := fLT_load_le c vx; omega
  | load32 x | loadByte x =>
    obtain ⟨k, hk, hb⟩ := ih x (by show sizeOf x < _; simp) tmp live
    first | rw [nodeT.eq_9] | rw [nodeT.eq_10]
    rcases hc : compileExpHOLExact ctxt tmp live x with ⟨cx, vx, nx, lx⟩
    rw [hc] at hk hb
    simp only [] at hk hb
    refine ⟨k + (fLT c vx + (24 + 0)), ?_, ?_⟩
    · simp only [compileExpHOLExact, hc, tightWorks_append, hk]
      rfl
    · simp only [compileExpHOLExact, hc, fLT.eq_2]; omega
  | shift s a b =>
    obtain ⟨ka, hka, hba⟩ := ih a (by show sizeOf a < _; simp; omega) tmp live
    rcases hca : compileExpHOLExact ctxt tmp live a with ⟨ca, va, na, la⟩
    rw [hca] at hka hba
    simp only [] at hka hba
    obtain ⟨kb, hkb, hbb⟩ := ih b (by show sizeOf b < _; simp) na la
    rcases hcb : compileExpHOLExact ctxt na la b with ⟨cb, vb, nb, lb⟩
    rw [hcb] at hkb hbb
    simp only [] at hkb hbb
    refine ⟨ka + kb, by simp [compileExpHOLExact, hca, hcb, tightWorks_append, hka, hkb], ?_⟩
    simp only [compileExpHOLExact, hca, hcb]
    by_cases hc : ∃ n, b = .const n
    · obtain ⟨n, rfl⟩ := hc
      simp only [compileExpHOLExact] at hcb
      cases hcb
      rw [fLT.eq_9, nodeT.eq_11]
      have : kb = 0 := by simpa [tightWorks_nil] using hkb.symm
      split_ifs <;> omega
    · have hvb : ∀ n, vb ≠ .const n := by
        have := comp_value_nonconst ctxt na la b (fun n h => hc ⟨n, h⟩); rw [hcb] at this; exact this
      rw [fLT.eq_10 c s va vb (fun n h => hvb n h), nodeT.eq_12 c s a b (fun n h => hc ⟨n, h⟩)]
      omega
  | op o ls =>
    rcases ls with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
    · rw [nodeT.eq_17] <;> first | exact tight_fallback c ctxt tmp live _ | (intros; simp_all)
    · rw [nodeT.eq_17] <;> first | exact tight_fallback c ctxt tmp live _ | (intros; simp_all)
    · obtain ⟨ka, hka, hba⟩ := ih a (by show sizeOf a < _; simp; omega) tmp live
      rcases hca : compileExpHOLExact ctxt tmp live a with ⟨ca, va, na, la⟩
      rw [hca] at hka hba
      simp only [] at hka hba
      obtain ⟨kb, hkb, hbb⟩ := ih b (by show sizeOf b < _; simp; omega) na la
      rcases hcb : compileExpHOLExact ctxt na la b with ⟨cb, vb, nb, lb⟩
      rw [hcb] at hkb hbb
      simp only [] at hkb hbb
      have hcode : (tightAllowance c).works (compileExpHOLExact ctxt tmp live (.op o [a, b])).1 = some (ka + kb) := by
        simp [compileExpHOLExact, comp_two, hca, hcb, tightWorks_append, hka, hkb]
      have hval : (compileExpHOLExact ctxt tmp live (.op o [a, b])).2.1 = .op o [va, vb] := by
        simp [compileExpHOLExact, comp_two, hca, hcb]
      by_cases hc : ∃ w, b = .const w
      · obtain ⟨w, rfl⟩ := hc
        simp only [compileExpHOLExact] at hcb
        cases hcb
        have : kb = 0 := by simpa [tightWorks_nil] using hkb.symm
        by_cases ho : o = .sub
        · subst ho
          refine ⟨ka + kb, hcode, ?_⟩
          rw [hval, fLT.eq_11, nodeT.eq_13]; omega
        · rw [nodeT.eq_15 c o a w ho]
          split_ifs with hs
          · have hsv := comp_value_safe ctxt tmp live o a hs
            rw [hca] at hsv
            refine ⟨ka + kb, hcode, ?_⟩
            rw [hval, fLT.eq_13 c o va w ho, if_pos hsv]; omega
          · exact tight_fallback c ctxt tmp live _
      · have hvb : ∀ w, vb ≠ .const w := by
          have := comp_value_nonconst ctxt na la b (fun w h => hc ⟨w, h⟩); rw [hcb] at this; exact this
        by_cases ho : o = .sub
        · subst ho
          refine ⟨ka + kb, hcode, ?_⟩
          rw [hval, fLT.eq_12 c va vb (fun w h => hvb w h), nodeT.eq_14 c a b (fun w h => hc ⟨w, h⟩)]
          omega
        · rw [nodeT.eq_16 c o a b (fun w _ h => hc ⟨w, h⟩) ho (fun w h => hc ⟨w, h⟩)]
          split_ifs with hs
          · simp only [Bool.and_eq_true] at hs
            have hsa := comp_value_safe ctxt tmp live o a hs.1
            have hsb := comp_value_safe ctxt na la o b hs.2
            rw [hca] at hsa; rw [hcb] at hsb
            refine ⟨ka + kb, hcode, ?_⟩
            rw [hval, fLT.eq_14 c o va vb (fun w _ h => hvb w h) ho (fun w h => hvb w h)]
            simp [hsa, hsb]; omega
          · exact tight_fallback c ctxt tmp live _
    · rw [nodeT.eq_17] <;> first | exact tight_fallback c ctxt tmp live _ | (intros; simp_all)
  | crepOp o xs => rw [nodeT.eq_17] <;> first | exact tight_fallback c ctxt tmp live _ | (intros; simp_all)
  | cmp o x y => rw [nodeT.eq_17] <;> first | exact tight_fallback c ctxt tmp live _ | (intros; simp_all)

end Crep

section Leaves
variable (c : Compiler.Encoders.Asm.AsmConfigExact 64)

theorem isel_set_lineBoundT (temp : Nat) (st : WordStoreHOL) (e : WordLangExpHOL (BitVec 64)) :
    ∃ k, lineBound preAllocLeafBudget (WordInst.instSelectExecutable c temp (.set st e)) = some k ∧
      k ≤ selT c e + 12 := by
  simp only [WordInst.instSelectExecutable, selT]
  obtain ⟨k, hk, hle⟩ := isel_lineBoundT c temp temp (WordInst.flattenExp (WordInst.ExecutablePullExp.pullExpExecutable e))
  exact ⟨k + 12, by simp [lineBound, hk, isLeafProg, preAllocLeafBudget, WordToStack.refinedWordStackLeafBudget], by omega⟩

theorem isel_store_lineBoundT (temp v : Nat) (e : WordLangExpHOL (BitVec 64)) :
    ∃ k, lineBound preAllocLeafBudget (WordInst.instSelectExecutable c temp (.store e v)) = some k ∧
      k ≤ selT c e + 24 := by
  have leaf : ∀ a w, lineBound preAllocLeafBudget (WordLangProgHOL.inst (WordLangInst.mem WordMemOp.store v
      (WordLangAddr.addr a w)) : WordLangProgHOL (BitVec 64)) = some 24 := by
    intro a w; simp [lineBound, isLeafProg, preAllocLeafBudget, WordToStack.refinedWordStackLeafBudget,
      WordToStack.refinedNativeInstructionPrice, Compiler.Encoders.Asm.HolInst.ofWordLangInst]
  simp only [WordInst.instSelectExecutable, selT]
  split
  · rename_i exp' w heq
    split
    · obtain ⟨k, hk, hle⟩ := isel_lineBoundT c temp temp exp'
      have := iselT_op_add_le c exp' w
      refine ⟨k + 24, by rw [lineBound, hk, leaf], ?_⟩
      rw [heq]; omega
    · obtain ⟨k, hk, hle⟩ := isel_lineBoundT c temp temp (.op .add [exp', .const w])
      exact ⟨k + 24, by rw [lineBound, heq, hk, leaf], by rw [heq]; omega⟩
  · obtain ⟨k, hk, hle⟩ := isel_lineBoundT c temp temp
      (WordInst.flattenExp (WordInst.ExecutablePullExp.pullExpExecutable e))
    exact ⟨k + 24, by rw [lineBound, hk, leaf], by omega⟩

theorem isel_share_lineBoundT (temp : Nat) (op : WordMemOp) (v : Nat) (e : WordLangExpHOL (BitVec 64)) :
    ∃ k, lineBound preAllocLeafBudget (WordInst.instSelectExecutable c temp (.shareInst op v e)) = some k ∧
      k ≤ selT c e + 13 := by
  have leaf : ∀ a, lineBound preAllocLeafBudget (.shareInst op v a) = some 13 := by
    intro a; simp [lineBound, isLeafProg, preAllocLeafBudget, WordToStack.refinedWordStackLeafBudget]
  simp only [WordInst.instSelectExecutable, selT]
  split
  · rename_i exp' w heq
    split
    · obtain ⟨k, hk, hle⟩ := isel_lineBoundT c temp temp exp'
      have := iselT_op_add_le c exp' w
      refine ⟨k + 13, by rw [lineBound, hk, leaf], ?_⟩
      rw [heq]; omega
    · obtain ⟨k, hk, hle⟩ := isel_lineBoundT c temp temp (.op .add [exp', .const w])
      exact ⟨k + 13, by rw [lineBound, heq, hk, leaf], by rw [heq]; omega⟩
  · obtain ⟨k, hk, hle⟩ := isel_lineBoundT c temp temp
      (WordInst.flattenExp (WordInst.ExecutablePullExp.pullExpExecutable e))
    exact ⟨k + 13, by rw [lineBound, hk, leaf], by omega⟩

theorem leafPL_setGlobalT (a : BitVec 5) (v : HolLoopExp 64) :
    ∃ k, leafPL c wsT1 wsT2 (.setGlobal a v) = some k ∧ k ≤ fLT c v + 12 := by
  refine ⟨iselX c (.set (.temp a) (LoopToWord.compExpHOL .ln v)), ?_, ?_⟩
  · simp [leafPL, loopWorkLeafCost, LoopToWord.compHOL, lineBound, isLeafProg, leafNodeB, isExprStmt, nodeEnv,
      siteKey]
  · obtain ⟨k, hk, hle⟩ := isel_set_lineBoundT c 0 (.temp a) (LoopToWord.compExpHOL .ln v)
    have := selT_le_fLT c .ln v
    exact iselX_le_of hk (by omega)

theorem leafPL_storeT (e : HolLoopExp 64) (v : Nat) :
    ∃ k, leafPL c wsT1 wsT2 (.store e v) = some k ∧ k ≤ fLT c e + 24 := by
  refine ⟨iselX c (.store (LoopToWord.compExpHOL .ln e) (LoopToWord.findVarHOL .ln v)), ?_, ?_⟩
  · simp [leafPL, loopWorkLeafCost, LoopToWord.compHOL, lineBound, isLeafProg, leafNodeB, isExprStmt, nodeEnv,
      siteKey]
  · obtain ⟨k, hk, hle⟩ := isel_store_lineBoundT c 0 (LoopToWord.findVarHOL .ln v) (LoopToWord.compExpHOL .ln e)
    have := selT_le_fLT c .ln e
    exact iselX_le_of hk (by omega)

theorem leafPL_shMemT (op : WordMemOp) (n : Nat) (e : HolLoopExp 64) :
    ∃ k, leafPL c wsT1 wsT2 (.shMem op n e) = some k ∧ k ≤ fLT c e + 13 := by
  refine ⟨iselX c (.shareInst op (LoopToWord.findVarHOL .ln n) (LoopToWord.compExpHOL .ln e)), ?_, ?_⟩
  · simp [leafPL, loopWorkLeafCost, LoopToWord.compHOL, lineBound, isLeafProg, leafNodeB, isExprStmt, nodeEnv,
      siteKey]
  · obtain ⟨k, hk, hle⟩ := isel_share_lineBoundT c 0 op (LoopToWord.findVarHOL .ln n) (LoopToWord.compExpHOL .ln e)
    have := selT_le_fLT c .ln e
    exact iselX_le_of hk (by omega)

end Leaves

/-- Sum of `fLT` over a list. -/
def fLTs (c : Compiler.Encoders.Asm.AsmConfigExact 64) (vs : List (HolLoopExp 64)) : Nat := (vs.map (fLT c)).sum

/-- Sum of `nodeT` over a list. -/
def nodeTs (c : Compiler.Encoders.Asm.AsmConfigExact 64) (es : List (CrepExpHOL 64)) : Nat := (es.map (nodeT c)).sum

theorem fLTs_cons (c : Compiler.Encoders.Asm.AsmConfigExact 64) (v : HolLoopExp 64) (vs : List (HolLoopExp 64)) :
    fLTs c (v :: vs) = fLT c v + fLTs c vs := by simp [fLTs]

theorem nodeTs_cons (c : Compiler.Encoders.Asm.AsmConfigExact 64) (e : CrepExpHOL 64) (es : List (CrepExpHOL 64)) :
    nodeTs c (e :: es) = nodeT c e + nodeTs c es := by simp [nodeTs]

theorem crep_to_loop_T_list (c : Compiler.Encoders.Asm.AsmConfigExact 64) (ctxt : CrepToLoopContextExact) :
    ∀ (es : List (CrepExpHOL 64)) (tmp : Nat) (live : NumSet),
    ∃ cost, (tightAllowance c).works (compileExpsHOLExact ctxt tmp live es).1 = some cost ∧
      cost + fLTs c (compileExpsHOLExact ctxt tmp live es).2.1 ≤ nodeTs c es
  | [], tmp, live => ⟨0, by simp [compileExpsHOLExact, tightWorks_nil], by simp [compileExpsHOLExact, fLTs, nodeTs]⟩
  | e :: es, tmp, live => by
    obtain ⟨a, ha, ba⟩ := crep_to_loop_T_work c ctxt e tmp live
    rcases he : compileExpHOLExact ctxt tmp live e with ⟨ce, ve, ne, le⟩
    rw [he] at ha ba
    simp only [] at ha ba
    obtain ⟨b, hb, bb⟩ := crep_to_loop_T_list c ctxt es ne le
    refine ⟨a + b, ?_, ?_⟩
    · simp [compileExpsHOLExact, he, tightWorks_append, ha, hb]
    · have hv : (compileExpsHOLExact ctxt tmp live (e :: es)).2.1 = ve :: (compileExpsHOLExact ctxt ne le es).2.1 := by
        simp [compileExpsHOLExact, he]
      rw [hv, fLTs_cons, nodeTs_cons]
      omega

theorem compileExps_length' (ctxt : CrepToLoopContextExact) :
    ∀ (es : List (CrepExpHOL 64)) (tmp : Nat) (live : NumSet),
      (compileExpsHOLExact ctxt tmp live es).2.1.length = es.length :=
  price_compileExps_length ctxt

/-- Argument-list price with the per-value move. -/
def nodeTsM (c : Compiler.Encoders.Asm.AsmConfigExact 64) (es : List (CrepExpHOL 64)) : Nat :=
  nodeTs c es + 39 * es.length

/-- The pattern-aware selector pricing of compiled Crep code at leaf price `wsLeaf c`. -/
noncomputable def tightPricing (c : Compiler.Encoders.Asm.AsmConfigExact 64) : LoopPricingG where
  L := wsLeaf c
  A := tightAllowance c
  vp := fLT c
  vps := fLTs c
  vps_nil := by simp [fLTs]
  vps_cons := fun v vs => by simp [fLTs]
  price := nodeT c
  priceList := nodeTsM c
  exprOk := fun context tmp live e => crep_to_loop_T_work c context e tmp live
  listOk := fun context tmp live es => by
    obtain ⟨cost, h, b⟩ := crep_to_loop_T_list c context es tmp live
    have len := compileExps_length' context es tmp live
    exact ⟨cost, h, by simp only [nodeTsM]; omega⟩
  assignWork := fun n v => ⟨fLT c v, rfl, Nat.le_refl _⟩
  assignOk := fun n v => leafPL_assignT c n v
  tickC := 6
  tickOk := ⟨6, (leafPL_simple c).2.1, Nat.le_refl _⟩
  breakC := 2
  breakOk := fun l => ⟨2, (leafPL_simple c).2.2.1 l, Nat.le_refl _⟩
  contC := 0
  contOk := fun l => ⟨0, (leafPL_simple c).2.2.2.1 l, Nat.le_refl _⟩
  constC := 24
  constOk := fun w => by rw [fLT.eq_1]
  raiseC := 63
  raiseOk := fun e => ⟨63, (leafPL_simple c).2.2.2.2.1 e, Nat.le_refl _⟩
  returnC := 15
  returnOk := fun vs => ⟨15, (leafPL_simple c).2.2.2.2.2.1 vs, Nat.le_refl _⟩
  setC := 12
  setOk := fun a v => leafPL_setGlobalT c a v
  shareC := 13
  shareOk := fun op n v => leafPL_shMemT c op n v
  storeC := 24
  storeOk := fun e v => leafPL_storeT c e v
  store32C := 24
  store32Ok := fun a v => ⟨24, (leafPL_simple c).2.2.2.2.2.2.1 a v, Nat.le_refl _⟩
  storeByteOk := fun a v => ⟨24, (leafPL_simple c).2.2.2.2.2.2.2 a v, Nat.le_refl _⟩
  ffiC := ffiSel
  ffiOk := fun f a b d e live => ⟨ffiSel, leafPL_ffi c f a b d e live, Nat.le_refl _⟩
  primC := 111
  primOk := fun ds op as => leafPL_primitive c ds op as


#print axioms tightCodeWork_bounded
#print axioms fLT_le_fL
#print axioms tightWorks_le
#print axioms crep_to_loop_T_work
#print axioms tightPricing
end InitECandidate.Runtime.FineCost
