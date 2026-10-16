import InitECandidate.Runtime.StackToLabIf
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.If

namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs

/-- The actual source comparison, including successful operand lookups. -/
def BranchCondition {width : Nat} [NeZero width] {C F : Type}
    (cmp : HolCmp) (reg : Nat) (ri : HolRegImm width)
    (s : StackSemStateFiniteExact width C F) (branch : Bool) : Prop :=
  ∃ x y, StackSemStateOps.getVar reg s = some x ∧
    StackSemStateOps.getVarImm (HolRegImm.toWordRegImm ri) s = some y ∧
    wordSemWordCmp cmp x y = some branch

section
variable {width : Nat} [NeZero width] {C F : Type}
/-- Only the branch selected by the actual source condition needs its budget.
This avoids charging execution work for an unselected branch. -/
theorem flattenIf_guarded_bounded (s1 : StackSemStateFiniteExact width C F) (cmp : HolCmp) (reg : Nat)
    (ri : HolRegImm width) (c1 c2 : HolProg width)
    (budget : Nat) (first : BranchCondition cmp reg ri s1 true → BoundedFlattenProp c1 s1 budget)
    (second : BranchCondition cmp reg ri s1 false → BoundedFlattenProp c2 s1 budget) :
    BoundedFlattenProp (.ite cmp reg ri c1 c2) s1 (budget + 2) := by
  rintro t res s2 n l cs bs t1 ⟨ev, nerr, rel, ca, inst, labs⟩
  rw [StackSemEvaluate.evaluate_ite] at ev
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at ca
  have err : ∀ {x : StackSemStateFiniteExact width C F},
      (some StackSemResult.error, x) = (res, s2) → False := fun e => by
    simp only [Prod.mk.injEq] at e; exact nerr e.1.symm
  split at ev
  swap; · exact (err ev).elim
  rename_i x y hx hy
  have rx : t1.regs reg = x := InstCorrect.regOfLookup rel hx
  have ry : regImm ri t1 = y := StateRel.stateRelGetVarImm ⟨rel, hy⟩
  rcases hc : wordSemWordCmp cmp x y with _ | b
  · rw [hc] at ev; exact (err ev).elim
  have branchChosen : BranchCondition cmp reg ri s1 b := ⟨x, y, hx, hy, hc⟩
  have hcmp : wordSemWordCmp cmp (t1.regs reg) (regImm ri t1) = some b := by rw [rx, ry, hc]
  have hneg : wordSemWordCmp (Flapjack.Compiler.Backend.StackToLab.negateHOL cmp) (t1.regs reg) (regImm ri t1) = some (!b) := by
    rw [Prelude.wordCmpNegate, hcmp]; rfl
  have lt1 : MeasureLt c1 s1 (.ite cmp reg ri c1 c2) s1 :=
    .inr ⟨rfl, StackSemMeasure.if_first_size_lt cmp reg ri c1 c2⟩
  have lt2 : MeasureLt c2 s1 (.ite cmp reg ri c1 c2) s1 :=
    .inr ⟨rfl, StackSemMeasure.if_second_size_lt cmp reg ri c1 c2⟩
  have evb : StackSemEvaluate.evaluate (if b then c1 else c2, s1) = (res, s2) := by
    rw [hc] at ev; cases b <;> exact ev
  rcases h1 : Flapjack.Compiler.Backend.StackToLab.flattenHOL false c1 n l cs bs with ⟨xs, nr1, l1⟩
  rcases h2 : Flapjack.Compiler.Backend.StackToLab.flattenHOL false c2 n l1 cs bs with ⟨ys, nr2, l2⟩
  have unfold := (show Flapjack.Compiler.Backend.StackToLab.flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs =
      Flapjack.Compiler.Backend.StackToLab.flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs from rfl)
  conv at unfold => rhs; rw [Flapjack.Compiler.Backend.StackToLab.flattenHOL]
  simp only [h1, h2] at unfold
  have nolab : ∀ (a : AsmWithLab HolCmp (HolRegImm width) Basis.Pure.MlString.MlString),
      isLabelHOL (Line.labAsm a 0 [] 0 : LabLineHOL width) = false := fun _ => rfl
  have hlenOf : ∀ (L : List (LabLineHOL width)),
      appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs).1 = L →
      ((appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs).1).filter
        (fun x => !isLabelHOL x)).length = (L.filter (fun x => !isLabelHOL x)).length :=
    fun L h => by rw [h]
  split_ifs at unfold with k1 k2 k3 k4 k5
  · -- both branches `Skip`
    simp only [Bool.and_eq_true] at k1
    rw [isSkipEq k1.1, isSkipEq k1.2] at evb
    have : (if b then (Flapjack.Compiler.Backend.StackLang.Prog.skip : HolProg width) else .skip) = .skip := by cases b <;> rfl
    rw [this, StackSemEvaluate.evaluate_skip] at evb
    simp only [Prod.mk.injEq] at evb
    obtain ⟨rfl, rfl⟩ := evb
    exact boundedFlattenConclStay (budget + 2) rel (by rw [unfold]; simp [appListAppendList])
  · -- then-branch `Skip`
    have hflat : appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs).1 =
        .labAsm (.jumpCmp cmp reg ri (.lab n l2)) 0 [] 0 :: (appListAppend ys ++
          [.label n l2 0]) := by
      rw [unfold]; simp [appListAppendAppend, appListAppendList]
    rw [hflat] at inst
    obtain ⟨fetch0, instRest⟩ := lineAt (nolab _) inst
    obtain ⟨instYs, instLab⟩ := codeInstalledAppendImp _ _ _ _ instRest
    obtain ⟨locL, -⟩ := labelAt instLab
    cases b
    · -- condition false: run the else-branch after the fall-through
      have step := fun c => (jumpCmpStep (b := false) c fetch0 hcmp)
      simp only [Bool.false_eq_true, if_false] at step
      refine ifCompose budget (by decide) (runToPc step) rfl rfl rfl rfl rfl (List.prefix_refl _) ?_
        ((second branchChosen) false res s2 n l1 cs bs { t1 with pc := t1.pc + 1 }
          ⟨evb, nerr, rel, ca.2, by rw [h2]; exact instYs, labs⟩)
      rw [hlenOf _ hflat, h2]
      simp [List.filter_append, isLabelHOL]
      omega
    · -- condition true: jump over the else-branch
      simp only [if_true] at evb
      rw [isSkipEq k2, StackSemEvaluate.evaluate_skip] at evb
      simp only [Prod.mk.injEq] at evb
      obtain ⟨rfl, rfl⟩ := evb
      have step := fun c => (jumpCmpStep (b := true) c fetch0 hcmp)
      simp only [if_true, locL] at step
      refine ⟨1, by omega, { t1 with pc := t1.pc + 1 + ((appListAppend ys).filter
          (fun x => !isLabelHOL x)).length }, runToPc step, rfl, rfl, rfl, rfl, rfl,
        List.prefix_refl _, ?_, rel⟩
      rw [hlenOf _ hflat]
      simp [List.filter_append, isLabelHOL]
      omega
  · -- else-branch `Skip`
    have hflat : appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs).1 =
        .labAsm (.jumpCmp (Flapjack.Compiler.Backend.StackToLab.negateHOL cmp) reg ri (.lab n l2)) 0 [] 0 :: (appListAppend xs ++
          [.label n l2 0]) := by
      rw [unfold]; simp [appListAppendAppend, appListAppendList]
    rw [hflat] at inst
    obtain ⟨fetch0, instRest⟩ := lineAt (nolab _) inst
    obtain ⟨instXs, instLab⟩ := codeInstalledAppendImp _ _ _ _ instRest
    obtain ⟨locL, -⟩ := labelAt instLab
    cases b
    · -- condition false: the negated test jumps over the then-branch
      simp only [Bool.false_eq_true, if_false] at evb
      rw [isSkipEq k3, StackSemEvaluate.evaluate_skip] at evb
      simp only [Prod.mk.injEq] at evb
      obtain ⟨rfl, rfl⟩ := evb
      have step := fun c => (jumpCmpStep (b := true) c fetch0 hneg)
      simp only [if_true, locL] at step
      refine ⟨1, by omega, { t1 with pc := t1.pc + 1 + ((appListAppend xs).filter
          (fun x => !isLabelHOL x)).length }, runToPc step, rfl, rfl, rfl, rfl, rfl,
        List.prefix_refl _, ?_, rel⟩
      rw [hlenOf _ hflat]
      simp [List.filter_append, isLabelHOL]
      omega
    · -- condition true: fall through into the then-branch
      have step := fun c => (jumpCmpStep (b := false) c fetch0 hneg)
      simp only [Bool.false_eq_true, if_false] at step
      refine ifCompose budget (by decide) (runToPc step) rfl rfl rfl rfl rfl (List.prefix_refl _) ?_
        ((first branchChosen) false res s2 n l cs bs { t1 with pc := t1.pc + 1 }
          ⟨evb, nerr, rel, ca.1, by rw [h1]; exact instXs, labs⟩)
      rw [hlenOf _ hflat, h1]
      simp [List.filter_append, isLabelHOL]
      omega
  · -- then-branch never returns: placed first
    have hflat : appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs).1 =
        .labAsm (.jumpCmp (Flapjack.Compiler.Backend.StackToLab.negateHOL cmp) reg ri (.lab n l2)) 0 [] 0 :: (appListAppend xs ++
          (.label n l2 0 :: appListAppend ys)) := by
      rw [unfold]; simp [appListAppendAppend, appListAppendList]
    rw [hflat] at inst
    obtain ⟨fetch0, instRest⟩ := lineAt (nolab _) inst
    obtain ⟨instXs, instLab⟩ := codeInstalledAppendImp _ _ _ _ instRest
    obtain ⟨locL, instYs⟩ := labelAt instLab
    cases b
    · -- condition false: jump to the else-branch
      have step := fun c => (jumpCmpStep (b := true) c fetch0 hneg)
      simp only [if_true, locL] at step
      refine ifCompose budget (by decide) (runToPc step) rfl rfl rfl rfl rfl (List.prefix_refl _) ?_
        ((second branchChosen) false res s2 n l1 cs bs _
          ⟨evb, nerr, rel, ca.2, by rw [h2]; exact instYs, labs⟩)
      rw [hlenOf _ hflat, h2]
      simp [List.filter_append, isLabelHOL]
      omega
    · -- condition true: the then-branch produces a result
      have some_ := FlattenHelpers.noRetCorrect false c1 n l cs bs (by rw [h1]; exact k4) s1
      simp only [if_true] at evb
      rw [evb] at some_
      obtain ⟨x, rfl⟩ := Option.isSome_iff_exists.mp some_
      have step := fun c => (jumpCmpStep (b := false) c fetch0 hneg)
      simp only [Bool.false_eq_true, if_false] at step
      exact ifComposeSome budget (by decide) (runToPc step) rfl rfl rfl rfl rfl (List.prefix_refl _)
        ((first branchChosen) false (some x) s2 n l cs bs { t1 with pc := t1.pc + 1 }
          ⟨evb, nerr, rel, ca.1, by rw [h1]; exact instXs, labs⟩)
  · -- else-branch never returns: placed first
    have hflat : appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs).1 =
        .labAsm (.jumpCmp cmp reg ri (.lab n l2)) 0 [] 0 :: (appListAppend ys ++
          (.label n l2 0 :: appListAppend xs)) := by
      rw [unfold]; simp [appListAppendAppend, appListAppendList]
    rw [hflat] at inst
    obtain ⟨fetch0, instRest⟩ := lineAt (nolab _) inst
    obtain ⟨instYs, instLab⟩ := codeInstalledAppendImp _ _ _ _ instRest
    obtain ⟨locL, instXs⟩ := labelAt instLab
    cases b
    · -- condition false: the else-branch produces a result
      have some_ := FlattenHelpers.noRetCorrect false c2 n l1 cs bs (by rw [h2]; exact k5) s1
      simp only [Bool.false_eq_true, if_false] at evb
      rw [evb] at some_
      obtain ⟨x, rfl⟩ := Option.isSome_iff_exists.mp some_
      have step := fun c => (jumpCmpStep (b := false) c fetch0 hcmp)
      simp only [Bool.false_eq_true, if_false] at step
      exact ifComposeSome budget (by decide) (runToPc step) rfl rfl rfl rfl rfl (List.prefix_refl _)
        ((second branchChosen) false (some x) s2 n l1 cs bs { t1 with pc := t1.pc + 1 }
          ⟨evb, nerr, rel, ca.2, by rw [h2]; exact instYs, labs⟩)
    · -- condition true: jump to the then-branch
      have step := fun c => (jumpCmpStep (b := true) c fetch0 hcmp)
      simp only [if_true, locL] at step
      refine ifCompose budget (by decide) (runToPc step) rfl rfl rfl rfl rfl (List.prefix_refl _) ?_
        ((first branchChosen) false res s2 n l cs bs _
          ⟨evb, nerr, rel, ca.1, by rw [h1]; exact instXs, labs⟩)
      rw [hlenOf _ hflat, h1]
      simp [List.filter_append, isLabelHOL]
      omega
  · -- general shape with a join jump
    have hflat : appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs).1 =
        .labAsm (.jumpCmp cmp reg ri (.lab n l2)) 0 [] 0 :: (appListAppend ys ++
          (.labAsm (.jump (.lab n (l2 + 1))) 0 [] 0 :: .label n l2 0 ::
            (appListAppend xs ++ [.label n (l2 + 1) 0]))) := by
      rw [unfold]; simp [appListAppendAppend, appListAppendList]
    rw [hflat] at inst
    obtain ⟨fetch0, instRest⟩ := lineAt (nolab _) inst
    obtain ⟨instYs, instRest2⟩ := codeInstalledAppendImp _ _ _ _ instRest
    obtain ⟨fetchJ, instRest3⟩ := lineAt (nolab _) instRest2
    obtain ⟨locL, instRest4⟩ := labelAt instRest3
    obtain ⟨instXs, instLab2⟩ := codeInstalledAppendImp _ _ _ _ instRest4
    obtain ⟨locL2, -⟩ := labelAt instLab2
    have total : ((appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs).1).filter
        (fun x => !isLabelHOL x)).length =
        ((appListAppend ys).filter (fun x => !isLabelHOL x)).length +
          ((appListAppend xs).filter (fun x => !isLabelHOL x)).length + 2 := by
      rw [hflat]; simp [List.filter_append, isLabelHOL]; omega
    cases b
    · -- condition false: the else-branch, then the join jump
      simp only [Bool.false_eq_true, if_false] at evb
      have step := fun c => (jumpCmpStep (b := false) c fetch0 hcmp)
      simp only [Bool.false_eq_true, if_false] at step
      have c2h := (second branchChosen) false res s2 n l1 cs bs { t1 with pc := t1.pc + 1 }
        ⟨evb, nerr, rel, ca.2, by rw [h2]; exact instYs, labs⟩
      cases res with
      | some x =>
        exact ifComposeSome budget (by decide) (runToPc step) rfl rfl rfl rfl rfl (List.prefix_refl _) c2h
      | none =>
        obtain ⟨ck2, bound2, t3, run2, f1, f2, f3, f4, f5, pre2, hpc2, rel3⟩ := c2h
        rw [h2] at hpc2
        simp only at hpc2 f1 f2 f3 f4 f5 pre2
        have fetchJ3 : asmFetchAux t3.pc t3.code =
            some (.labAsm (.jump (.lab n (l2 + 1))) 0 [] 0) := by
          rw [hpc2]; exact asmFetchAuxSomeIsPrefix _ _ _ _ ⟨fetchJ, pre2⟩
        have locL23 := locToPcIsPrefix _ _ _ _ _ ⟨locL2, pre2⟩
        refine ⟨1 + ck2 + 1, by omega, { t3 with pc := t1.pc + 1 +
            ((appListAppend ys).filter (fun x => !isLabelHOL x)).length + 1 +
            ((appListAppend xs).filter (fun x => !isLabelHOL x)).length },
          fun ck1 => ?_, f1, f2, f3, f4, f5, pre2, ?_, rel3⟩
        · rw [show t1.clock + (1 + ck2 + 1) + ck1 = t1.clock + 1 + (ck2 + (ck1 + 1)) by omega,
            runToPc step, show t1.clock + (ck2 + (ck1 + 1)) = t1.clock + ck2 + (ck1 + 1) by omega,
            run2, show t3.clock + (ck1 + 1) = (t3.clock + ck1) + 1 by omega,
            jumpStep (t3.clock + ck1) fetchJ3 locL23]
        · simp only [total]; omega
    · -- condition true: jump to the then-branch
      simp only [if_true] at evb
      have step := fun c => (jumpCmpStep (b := true) c fetch0 hcmp)
      simp only [if_true, locL] at step
      refine ifCompose budget (by decide) (runToPc step) rfl rfl rfl rfl rfl (List.prefix_refl _) ?_
        ((first branchChosen) false res s2 n l cs bs _
          ⟨evb, nerr, rel, ca.1, by rw [h1]; exact instXs, labs⟩)
      rw [total, h1]
      simp
      omega

end
#print axioms flattenIf_guarded_bounded
end InitECandidate.Runtime.StackToLab
