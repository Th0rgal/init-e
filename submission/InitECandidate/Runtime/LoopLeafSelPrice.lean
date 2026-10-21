import InitECandidate.Runtime.LoopLeafSelBound
import InitECandidate.Runtime.SourceCostLoopWorkWs
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend

/-! Selector prices of Loop expressions and leaves. `fL` is `fW` of the
compiled Word expression, independent of the variable context; it bounds the
selector-derived leaf price `leafPL` of a compiled assignment. -/

mutual
/-- Selector price of a Loop expression. -/
def fL : HolLoopExp 64 → Nat
  | .const _ | .var _ | .lookup _ | .baseAddr => 24
  | .topAddr => 124
  | .load a => fL a + 24
  | .op _ args => fLs args + 24 * (args.length - 1) + 24 * (1 - args.length)
  | .shift _ a b => fL a + fL b + 28

/-- Sum of `fL` over a list. -/
def fLs : List (HolLoopExp 64) → Nat
  | [] => 0
  | a :: as => fL a + fLs as
end

theorem fW_compExp (ctxt : Spt Nat) (e : HolLoopExp 64) : fW (LoopToWord.compExpHOL ctxt e) = fL e := by
  refine (measure (sizeOf : HolLoopExp 64 → Nat)).wf.induction (C := fun e =>
    fW (LoopToWord.compExpHOL ctxt e) = fL e) e ?_
  intro e ih
  cases e with
  | load a => rw [LoopToWord.compExpHOL]; simp only [fW, fL, ih a (by show sizeOf a < _; simp)]
  | shift sh a b =>
    rw [LoopToWord.compExpHOL]
    simp only [fW, fL, ih a (by show sizeOf a < _; simp; omega), ih b (by show sizeOf b < _; simp)]
  | op o args =>
    rw [LoopToWord.compExpHOL]
    have hl : ∀ L : List (HolLoopExp 64), (∀ a ∈ L, fW (LoopToWord.compExpHOL ctxt a) = fL a) →
        fWs (L.map (LoopToWord.compExpHOL ctxt)) = fLs L := by
      intro L
      induction L with
      | nil => intro _; simp [fWs, fLs]
      | cons a L ihL => intro h; simp only [List.map_cons, fWs, fLs, h a (by simp), ihL (fun b hb => h b (by simp [hb]))]
    simp only [fW, fL, List.length_map]
    rw [hl args (fun a ha => ih a (by have := List.sizeOf_lt_of_mem ha; show sizeOf a < _; simp; omega))]
  | const w => rw [LoopToWord.compExpHOL]; simp [fW, fL]
  | var v => rw [LoopToWord.compExpHOL]; simp [fW, fL]
  | lookup a => rw [LoopToWord.compExpHOL]; simp [fW, fL]
  | baseAddr => rw [LoopToWord.compExpHOL]; simp [fW, fL]
  | topAddr => rw [LoopToWord.compExpHOL]; simp [fW, fL, fWs]

#print axioms fW_compExp

theorem leafPL_assign (c : Compiler.Encoders.Asm.AsmConfigExact 64) (T1 T2 : SiteTable) (n : Nat) (v : HolLoopExp 64) :
    ∃ k, leafPL c T1 T2 (.assign n v) = some k ∧ k ≤ fL v := by
  refine ⟨iselX c (.assign (LoopToWord.findVarHOL .ln n) (LoopToWord.compExpHOL .ln v)), ?_, ?_⟩
  · simp [leafPL, loopWorkLeafCost, LoopToWord.compHOL, lineBound, isLeafProg, leafNodeB, isExprStmt, nodeEnv,
      siteKey]
  · rw [← fW_compExp .ln v]; exact iselX_assign_le c _ _

theorem leafPL_arith (c : Compiler.Encoders.Asm.AsmConfigExact 64) (T1 T2 : SiteTable) (op : LoopArith) :
    ∃ k, leafPL c T1 T2 (.arith op) = some k ∧ k ≤ 27 := by
  cases op <;> refine ⟨_, by simp [leafPL, loopWorkLeafCost, LoopToWord.compHOL, lineBound, isLeafProg, leafNodeB,
    isExprStmt, nodeEnv, siteKey, preAllocLeafBudget, WordToStack.refinedWordStackLeafBudget,
    Compiler.Encoders.Asm.HolInst.ofWordLangInst, Compiler.Encoders.Asm.HolArith.ofWordLangArith,
    WordToStack.refinedNativeInstructionPrice]; rfl, by decide⟩

theorem leafPL_load32 (c : Compiler.Encoders.Asm.AsmConfigExact 64) (T1 T2 : SiteTable) (a d : Nat) :
    leafPL c T1 T2 (.load32 a d) = some 24 := by
  simp [leafPL, loopWorkLeafCost, LoopToWord.compHOL, lineBound, isLeafProg, leafNodeB,
    isExprStmt, nodeEnv, siteKey, preAllocLeafBudget, WordToStack.refinedWordStackLeafBudget,
    Compiler.Encoders.Asm.HolInst.ofWordLangInst, WordToStack.refinedNativeInstructionPrice]

theorem leafPL_loadByte (c : Compiler.Encoders.Asm.AsmConfigExact 64) (T1 T2 : SiteTable) (a d : Nat) :
    leafPL c T1 T2 (.loadByte a d) = some 24 := by
  simp [leafPL, loopWorkLeafCost, LoopToWord.compHOL, lineBound, isLeafProg, leafNodeB,
    isExprStmt, nodeEnv, siteKey, preAllocLeafBudget, WordToStack.refinedWordStackLeafBudget,
    Compiler.Encoders.Asm.HolInst.ofWordLangInst, WordToStack.refinedNativeInstructionPrice]

#print axioms leafPL_assign

/-- Selector-priced allowance for expression-generated Loop code (the
selector analogue of `loopExpressionCodeWork`). -/
def selCodeWork : HolLoopProg 64 → Option Nat
  | .skip => some 0
  | .assign _ v => some (fL v)
  | .arith _ => some 27
  | .load32 _ _ | .loadByte _ _ => some 24
  | .seq a b => do
      let x ← selCodeWork a
      let y ← selCodeWork b
      pure (x + y)
  | .ite _ _ _ y n _ => do
      let a ← selCodeWork y
      let b ← selCodeWork n
      pure (37 + max a b)
  | _ => none

/-- A state-uniform executed-work ceiling at the selector-derived price, in
any calling function. -/
def LoopBoundedS (c : Compiler.Encoders.Asm.AsmConfigExact 64) (p : HolLoopProg 64) (bound : Nat) : Prop :=
  ∀ (F : Type) (f : Nat) (s : LoopSemStateFiniteExact 64 F), ∃ w,
    LoopWorkG (wsLeaf c) f s p (LoopSemStateFiniteExact.evaluate p s) w ∧ w ≤ bound

theorem loopBoundedS_leaf {c : Compiler.Encoders.Asm.AsmConfigExact 64} {p : HolLoopProg 64} {k b : Nat}
    (leaf : leafPL c wsT1 wsT2 p = some k) (le : k ≤ b) : LoopBoundedS c p b :=
  fun _ _ s => ⟨k, LoopWorkG.atom leaf rfl, le⟩

theorem loopBoundedS_seq {c : Compiler.Encoders.Asm.AsmConfigExact 64} {first second : HolLoopProg 64} {a b : Nat}
    (one : LoopBoundedS c first a) (two : LoopBoundedS c second b) :
    LoopBoundedS c (.seq first second) (a + b) := by
  intro F f s
  obtain ⟨w1, work1, bound1⟩ := one F f s
  rcases run : LoopSemStateFiniteExact.evaluate first s with ⟨_ | result, middle⟩
  · rw [run] at work1
    obtain ⟨w2, work2, bound2⟩ := two F f middle
    refine ⟨w1 + w2, ?_, by omega⟩
    have rule := LoopWorkG.seqNext work1 work2
    rwa [← LoopWorkG.sound rule] at rule
  · rw [run] at work1
    refine ⟨w1, ?_, by omega⟩
    have rule := LoopWorkG.seqStop (second := second) work1
    rwa [← LoopWorkG.sound rule] at rule

theorem loopBoundedS_ite {c : Compiler.Encoders.Asm.AsmConfigExact 64} {operator : Cmp} {register : Nat}
    {right : RegImm (BitVec 64)} {yes no : HolLoopProg 64} {live : NumSet} {a b : Nat}
    (yesB : LoopBoundedS c yes a) (noB : LoopBoundedS c no b) :
    LoopBoundedS c (.ite operator register right yes no live) (37 + max a b) := by
  intro F f s
  by_cases words : ∃ x y, sptLookup register s.locals = some (.word x) ∧
      LoopSemStateFiniteExact.getVarImm right s = some (.word y)
  · obtain ⟨x, y, hx, hy⟩ := words
    by_cases chosen : Compiler.Encoders.Asm.wordCmpHOL operator x y = true
    · obtain ⟨w, work, bound⟩ := yesB F f s
      have rule := LoopWorkG.iteBranch (live := live) (no := no) hx hy (by rw [if_pos chosen]; exact work)
      refine ⟨37 + w, ?_, by omega⟩
      rwa [← LoopWorkG.sound rule] at rule
    · obtain ⟨w, work, bound⟩ := noB F f s
      have rule := LoopWorkG.iteBranch (live := live) (yes := yes) hx hy (by rw [if_neg chosen]; exact work)
      refine ⟨37 + w, ?_, by omega⟩
      rwa [← LoopWorkG.sound rule] at rule
  · have rule := LoopWorkG.iteInvalid (L := wsLeaf c) (f := f) (live := live) (yes := yes) (no := no)
      (operator := operator) (s := s) words
    refine ⟨1, ?_, by omega⟩
    rwa [← LoopWorkG.sound rule] at rule

/-- Selector-priced expression code is executed within its allowance. -/
theorem selCodeWork_bounded (c : Compiler.Encoders.Asm.AsmConfigExact 64) :
    ∀ (p : HolLoopProg 64) (k : Nat), selCodeWork p = some k → LoopBoundedS c p k
  | .skip, k, h => by
    simp only [selCodeWork, Option.some.injEq] at h; subst h
    exact loopBoundedS_leaf (by simp [leafPL, loopWorkLeafCost, LoopToWord.compHOL, lineBound, isLeafProg,
      leafNodeB, isExprStmt, nodeEnv, siteKey, preAllocLeafBudget, WordToStack.refinedWordStackLeafBudget]) (Nat.le_refl _)
  | .assign n v, k, h => by
    simp only [selCodeWork, Option.some.injEq] at h; subst h
    obtain ⟨k', hk, hle⟩ := leafPL_assign c wsT1 wsT2 n v
    exact loopBoundedS_leaf hk hle
  | .arith op, k, h => by
    simp only [selCodeWork, Option.some.injEq] at h; subst h
    obtain ⟨k', hk, hle⟩ := leafPL_arith c wsT1 wsT2 op
    exact loopBoundedS_leaf hk hle
  | .load32 a d, k, h => by
    simp only [selCodeWork, Option.some.injEq] at h; subst h
    exact loopBoundedS_leaf (leafPL_load32 c wsT1 wsT2 a d) (Nat.le_refl _)
  | .loadByte a d, k, h => by
    simp only [selCodeWork, Option.some.injEq] at h; subst h
    exact loopBoundedS_leaf (leafPL_loadByte c wsT1 wsT2 a d) (Nat.le_refl _)
  | .seq a b, k, h => by
    simp only [selCodeWork] at h
    rcases ha : selCodeWork a with _ | x <;> rcases hb : selCodeWork b with _ | y <;> simp [ha, hb] at h
    subst h
    exact loopBoundedS_seq (selCodeWork_bounded c a x ha) (selCodeWork_bounded c b y hb)
  | .ite op r ri yes no live, k, h => by
    simp only [selCodeWork] at h
    rcases ha : selCodeWork yes with _ | x <;> rcases hb : selCodeWork no with _ | y <;> simp [ha, hb] at h
    subst h
    exact loopBoundedS_ite (selCodeWork_bounded c yes x ha) (selCodeWork_bounded c no y hb)
  | .loop _ _ _, k, h | .mark _, k, h | .call _ _ _ _, k, h | .primitive _ _ _, k, h | .store _ _, k, h
  | .setGlobal _ _, k, h | .store32 _ _, k, h | .storeByte _ _, k, h | .break _, k, h | .continue _, k, h
  | .raise _, k, h | .return _, k, h | .shMem _ _ _, k, h | .tick, k, h | .fail, k, h | .locValue _ _, k, h
  | .ffi _ _ _ _ _ _, k, h => by simp [selCodeWork] at h

#print axioms selCodeWork_bounded
end InitECandidate.Runtime.FineCost
