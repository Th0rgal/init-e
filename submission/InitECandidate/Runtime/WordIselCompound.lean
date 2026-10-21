import InitECandidate.Runtime.WordIselTransfer
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact

/-! Compound cases of the instruction-selection transfer. `IselGoal` is the
transfer for one program from any related state lexicographically at or below
`(td, ck)`, given the callee hypothesis at `(td, ck)`. Each step derives the
goal for a compound node from the goals of its sub-programs. -/

/-- `(a, b)` is lexicographically at most `(c, d)`. -/
def LexLe (a b c d : Nat) : Prop := a < c ∨ (a = c ∧ b ≤ d)

/-- The transfer for one program from any related state at or below `(td, ck)`,
given the callee hypothesis at `(td, ck)`. -/
def IselGoal {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (td ck temp : Nat)
    (p : WordLangProgHOL (BitVec 64)) : Prop :=
  IselCalleeIH (C := C) (F := F) c td ck →
  ∀ (s t : WordSemStateFiniteExact 64 C F) (res : Option (WordSemResult 64)) (rst : WordSemStateFiniteExact 64 C F),
    LexLe s.termdep s.clock td ck →
    everyVarHOL (fun x => decide (x < temp)) p = true → IselRel c temp s t →
    evaluate p s = (res, rst) → res ≠ some .error →
    ∃ rstT, evaluate (WordInst.instSelectExecutable c temp p) t = (res, rstT) ∧
      IselPost c temp res rst rstT ∧
      wordExecutionCost wordOptimizerLocalPrice (WordInst.instSelectExecutable c temp p) t ≤
        wordExecutionCost (preIselPrice c) p s

theorem iselPost_rel {C F : Type} {c : Compiler.Encoders.Asm.AsmConfigExact 64} {temp : Nat}
    {s t : WordSemStateFiniteExact 64 C F} (h : IselPost c temp none s t) : IselRel c temp s t := h

theorem evaluate_seq_some {C F : Type} (p q : WordLangProgHOL (BitVec 64)) (s s' : WordSemStateFiniteExact 64 C F)
    (r : WordSemResult 64) (h : evaluate p s = (some r, s')) : evaluate (.seq p q) s = (some r, s') := by
  have ht := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [ht, h]

theorem lexLe_of_run {C F : Type} {p : WordLangProgHOL (BitVec 64)} {s s' : WordSemStateFiniteExact 64 C F}
    {r : Option (WordSemResult 64)} {td ck : Nat} (h : evaluate p s = (r, s')) (le : LexLe s.termdep s.clock td ck) :
    LexLe s'.termdep s'.clock td ck := by
  obtain ⟨hc, ht⟩ := evaluate_clock p s r s' h
  rcases le with lt | ⟨eq, cle⟩
  · exact Or.inl (ht ▸ lt)
  · exact Or.inr ⟨ht ▸ eq, Nat.le_trans hc cle⟩

theorem isel_seq_step {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (td ck temp : Nat)
    (p1 p2 : WordLangProgHOL (BitVec 64)) (h1 : IselGoal (C := C) (F := F) c td ck temp p1)
    (h2 : IselGoal (C := C) (F := F) c td ck temp p2) : IselGoal (C := C) (F := F) c td ck temp (.seq p1 p2) := by
  intro ih s t res rst le vars rel run ok
  simp only [everyVarHOL, Bool.and_eq_true] at vars
  have sel : WordInst.instSelectExecutable c temp (.seq p1 p2) =
      .seq (WordInst.instSelectExecutable c temp p1) (WordInst.instSelectExecutable c temp p2) := by
    simp [WordInst.instSelectExecutable]
  rw [sel]
  rcases e1 : evaluate p1 s with ⟨r1, s1⟩
  cases r1 with
  | none =>
    rw [WordInst.evaluate_seq_none p1 p2 s s1 e1] at run
    obtain ⟨t1, ht1, post1, cost1⟩ := h1 ih s t none s1 le vars.1 rel e1 (by simp)
    obtain ⟨t2, ht2, post2, cost2⟩ := h2 ih s1 t1 res rst (lexLe_of_run e1 le) vars.2 post1 run ok
    refine ⟨t2, by rw [WordInst.evaluate_seq_none _ _ t t1 ht1]; exact ht2, post2, ?_⟩
    rw [wordExecutionCost_seq, wordExecutionCost_seq, ht1, e1]
    simp only [wordOptimizerLocalPrice, preIselPrice, WordToStack.refinedWordLocalPrice,
      WordToStack.refinedWordStackLeafBudget]
    omega
  | some x =>
    rw [evaluate_seq_some p1 p2 s s1 x e1] at run
    simp only [Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    obtain ⟨t1, ht1, post1, cost1⟩ := h1 ih s t (some x) s1 le vars.1 rel e1 ok
    refine ⟨t1, evaluate_seq_some _ _ t t1 x ht1, post1, ?_⟩
    rw [wordExecutionCost_seq, wordExecutionCost_seq, ht1, e1]
    simp only [wordOptimizerLocalPrice, preIselPrice, WordToStack.refinedWordLocalPrice,
      WordToStack.refinedWordStackLeafBudget]
    omega

theorem getVar_rel {C F : Type} {c : Compiler.Encoders.Asm.AsmConfigExact 64} {temp x : Nat}
    {s t : WordSemStateFiniteExact 64 C F} (rel : IselRel c temp s t) (hx : x < temp) :
    getVar x t = getVar x s := by
  simp only [getVar]; exact (rel.1 x hx).symm

theorem isel_ite_step {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (td ck temp : Nat)
    (cmp : Cmp) (r1 : Nat) (ri : WordRegImm (BitVec 64)) (c1 c2 : WordLangProgHOL (BitVec 64))
    (h1 : IselGoal (C := C) (F := F) c td ck temp c1) (h2 : IselGoal (C := C) (F := F) c td ck temp c2) :
    IselGoal (C := C) (F := F) c td ck temp (.ite cmp r1 ri c1 c2) := by
  intro ih s t res rst le vars rel run ok
  have hi := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [everyVarHOL, Bool.and_eq_true, decide_eq_true_eq] at vars
  obtain ⟨⟨⟨hr1, hri⟩, hc1⟩, hc2⟩ := vars
  have gv := getVar_rel rel hr1
  have gi : WordSemStateFiniteExact.getVarImm ri t = WordSemStateFiniteExact.getVarImm ri s := by
    have codeFree : ∀ (X : WordSemStateFiniteExact 64 C F) (k : Spt (Nat × WordLangProgHOL (BitVec 64))),
        WordSemStateFiniteExact.getVarImm ri { X with code := k } = WordSemStateFiniteExact.getVarImm ri X := by
      intro X k; cases ri <;> rfl
    have base := locals_rel_get_var_imm_simp temp ri s t.locals ⟨hri, rel.1⟩
    have tx : t = { ({ s with locals := t.locals } : WordSemStateFiniteExact 64 C F) with code := t.code } := rel.2.2
    calc WordSemStateFiniteExact.getVarImm ri t
        = WordSemStateFiniteExact.getVarImm ri
            { ({ s with locals := t.locals } : WordSemStateFiniteExact 64 C F) with code := t.code } := by
          conv_lhs => rw [tx]
      _ = _ := (codeFree _ _).trans base
  have sel : WordInst.instSelectExecutable c temp (.ite cmp r1 ri c1 c2) =
      .ite cmp r1 ri (WordInst.instSelectExecutable c temp c1) (WordInst.instSelectExecutable c temp c2) := by
    simp [WordInst.instSelectExecutable]
  rw [sel]
  rw [hi] at run
  rcases hx : getVar r1 s with _ | x
  · simp only [hx, Prod.mk.injEq] at run; exact absurd run.1.symm ok
  rcases hy : WordSemStateFiniteExact.getVarImm ri s with _ | y
  · simp only [hx, hy, Prod.mk.injEq] at run; exact absurd run.1.symm ok
  simp only [hx, hy] at run
  rcases hw : wordSemWordCmp cmp x y with _ | (_ | _)
  · simp only [hw, Prod.mk.injEq] at run; exact absurd run.1.symm ok
  · simp only [hw] at run
    obtain ⟨tB, htB, post, cost⟩ := h2 ih s t res rst le hc2 rel run ok
    refine ⟨tB, by rw [hi, gv, gi, hx, hy]; simpa [hw] using htB, post, ?_⟩
    rw [wordExecutionCost, wordExecutionCost, gv, gi, hx, hy]
    simp only [hw, wordOptimizerLocalPrice, preIselPrice, WordToStack.refinedWordLocalPrice,
      WordToStack.refinedWordStackLeafBudget]
    omega
  · simp only [hw] at run
    obtain ⟨tB, htB, post, cost⟩ := h1 ih s t res rst le hc1 rel run ok
    refine ⟨tB, by rw [hi, gv, gi, hx, hy]; simpa [hw] using htB, post, ?_⟩
    rw [wordExecutionCost, wordExecutionCost, gv, gi, hx, hy]
    simp only [hw, wordOptimizerLocalPrice, preIselPrice, WordToStack.refinedWordLocalPrice,
      WordToStack.refinedWordStackLeafBudget]
    omega

theorem isel_mustTerminate_step {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (td ck temp : Nat)
    (p1 : WordLangProgHOL (BitVec 64)) (h1 : IselGoal (C := C) (F := F) c td ck temp p1) :
    IselGoal (C := C) (F := F) c td ck temp (.mustTerminate p1) := by
  intro ih s t res rst le vars rel run ok
  have hm := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
  simp only [everyVarHOL] at vars
  obtain ⟨hl, hcode, ht⟩ := rel
  have tdEq : t.termdep = s.termdep := by rw [ht]
  have ckEq : t.clock = s.clock := by rw [ht]
  have sel : WordInst.instSelectExecutable c temp (.mustTerminate p1) =
      .mustTerminate (WordInst.instSelectExecutable c temp p1) := by
    simp [WordInst.instSelectExecutable]
  rw [sel]
  rw [hm] at run
  by_cases hz : s.termdep = 0
  · rw [if_pos hz, Prod.mk.injEq] at run; exact absurd run.1.symm ok
  rw [if_neg hz] at run
  rcases hq : evaluate p1 { s with clock := wordSemMustTerminateLimit 64, termdep := s.termdep - 1 } with ⟨r1, s1⟩
  rw [hq] at run
  have key : r1 ≠ some .timeOut ∧ res = r1 ∧ rst = { s1 with clock := s.clock, termdep := s.termdep } := by
    rcases r1 with _ | (_ | _ | _ | _ | _ | _ | _ | _) <;> simp only [Prod.mk.injEq] at run <;>
      first
        | exact absurd run.1.symm ok
        | exact ⟨by simp, run.1.symm, run.2.symm⟩
  obtain ⟨hr1, rfl, rfl⟩ := key
  have bodyRel : IselRel c temp { s with clock := wordSemMustTerminateLimit 64, termdep := s.termdep - 1 }
      { t with clock := wordSemMustTerminateLimit 64, termdep := t.termdep - 1 } := by
    refine ⟨hl, hcode, ?_⟩
    rw [tdEq]; conv_lhs => rw [ht]
  have bodyLe : LexLe (s.termdep - 1) (wordSemMustTerminateLimit 64) td ck := by
    rcases le with lt | ⟨eq, _⟩ <;> left <;> omega
  obtain ⟨t1, ht1, post1, cost1⟩ := h1 ih _ _ res s1 bodyLe vars bodyRel hq ok
  refine ⟨{ t1 with clock := t.clock, termdep := t.termdep }, ?_, ?_, ?_⟩
  · rw [hm, if_neg (tdEq ▸ hz), ht1]
    rcases res with _ | (_ | _ | _ | _ | _ | _ | _ | _) <;> first | exact absurd rfl hr1 | rfl
  · obtain ⟨p1l, p1c, p1f⟩ := post1
    refine ⟨p1l, p1c, ?_⟩
    rw [ckEq, tdEq]; conv_lhs => rw [p1f]
  · rw [wordExecutionCost, wordExecutionCost, dif_neg (tdEq ▸ hz), dif_neg hz]
    simp only [wordOptimizerLocalPrice, preIselPrice, WordToStack.refinedWordLocalPrice,
      WordToStack.refinedWordStackLeafBudget]
    rw [tdEq] at *
    omega

#print axioms isel_seq_step
#print axioms isel_ite_step
#print axioms isel_mustTerminate_step
end InitECandidate.Runtime.FineCost
