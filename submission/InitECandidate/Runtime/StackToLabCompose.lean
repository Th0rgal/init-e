import InitECandidate.Runtime.StackToLabBudget
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.Control

namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs

section
variable {width : Nat} [NeZero width] {C F : Type}
theorem boundedFlattenConcl_mono {p : HolProg width} {t : Bool}
    {r : Option (StackSemResult width)} {s2 : StackSemStateFiniteExact width C F}
    {n l : Nat} {cs bs : List Nat} {t1 : Flapjack.Compiler.Backend.LabSem.State width C F}
    {a b : Nat} (le : a ≤ b) (h : BoundedFlattenConcl p t r s2 n l cs bs t1 a) :
    BoundedFlattenConcl p t r s2 n l cs bs t1 b := by
  obtain ⟨ck, bound, rest⟩ := h
  exact ⟨ck, bound.trans le, rest⟩

/-- The conclusion for a result does not depend on the program, tail flag
or next label. -/
theorem boundedFlattenConclSome {p p' : HolProg width} {t t' : Bool} {x : StackSemResult width}
    {s2 : StackSemStateFiniteExact width C F} {n l l' : Nat} {cs bs : List Nat}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (budget : Nat)
    (h : BoundedFlattenConcl p t (some x) s2 n l cs bs t1 budget) : BoundedFlattenConcl p' t' (some x) s2 n l' cs bs t1 budget := by
  obtain ⟨ck, bound, t2, h⟩ := h
  refine ⟨ck, bound, t2, ?_⟩
  revert h
  cases haltView (some x) with
  | some res => exact id
  | none =>
    simp only [Option.map_some]
    cases resultView x n cs bs <;> exact id

/-- Composition of a LabSem prefix run reaching `t2` with the conclusion of a
following sub-program started in `t2`. -/
theorem boundedFlattenConclCompose {p p' : HolProg width} {t t' : Bool}
    {r : Option (StackSemResult width)} {s2 : StackSemStateFiniteExact width C F}
    {n l l' : Nat} {cs bs : List Nat} {ck : Nat}
    {t1 t2 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (budget : Nat) (secondBudget : Nat) (firstBound : ck ≤ budget)
    (run : ∀ ck1, evaluate { t1 with clock := t1.clock + ck + ck1 } =
      evaluate { t2 with clock := t2.clock + ck1 })
    (e1 : t2.lenReg = t1.lenReg) (e2 : t2.ptrReg = t1.ptrReg) (e3 : t2.len2Reg = t1.len2Reg)
    (e4 : t2.ptr2Reg = t1.ptr2Reg) (e5 : t2.linkReg = t1.linkReg) (pre : t1.code <+: t2.code)
    (hlen : t1.pc + ((appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL t p n l cs bs).1).filter
        (fun x => !isLabelHOL x)).length =
      t2.pc + ((appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL t' p' n l' cs bs).1).filter
        (fun x => !isLabelHOL x)).length)
    (h : BoundedFlattenConcl p' t' r s2 n l' cs bs t2 secondBudget) : BoundedFlattenConcl p t r s2 n l cs bs t1 (budget + secondBudget) := by
  obtain ⟨ck', secondBound, t3, h⟩ := h
  refine ⟨ck + ck', by omega, t3, ?_⟩
  revert h
  cases haltView r with
  | some res =>
    rintro ⟨ev, ffi⟩
    refine ⟨?_, ffi⟩
    rw [← Nat.add_assoc, run ck', ev]
  | none =>
    rintro ⟨run2, f1, f2, f3, f4, f5, pre2, rest⟩
    refine ⟨fun ck1 => ?_, by rw [f1, e1], by rw [f2, e2], by rw [f3, e3], by rw [f4, e4],
      by rw [f5, e5], pre.trans pre2, ?_⟩
    · rw [show t1.clock + (ck + ck') + ck1 = t1.clock + ck + (ck' + ck1) by omega, run,
        ← run2 ck1, Nat.add_assoc]
    · revert rest
      cases r.map (fun w => resultView w n cs bs) with
      | none => rintro ⟨hpc, rel⟩; exact ⟨by omega, rel⟩
      | some v => cases v <;> exact id

/-- `Seq` case. -/
theorem flattenSeq_bounded (s1 : StackSemStateFiniteExact width C F) (c1 c2 : HolProg width)
    (firstBudget secondBudget : Nat)
    (first : BoundedFlattenProp c1 s1 firstBudget)
    (second : ∀ (middle : StackSemStateFiniteExact width C F), BoundedFlattenProp c2 middle secondBudget) :
    BoundedFlattenProp (.seq c1 c2) s1 (firstBudget + secondBudget) := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, ca, inst, labs⟩
  rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate] at ev
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at ca
  rcases h1 : Flapjack.Compiler.Backend.StackToLab.flattenHOL false c1 n l cs bs with ⟨xs, nr1, l1⟩
  rcases h2 : Flapjack.Compiler.Backend.StackToLab.flattenHOL false c2 n l1 cs bs with ⟨ys, nr2, l2⟩
  have hflat : appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL t (.seq c1 c2) n l cs bs).1 =
      appListAppend xs ++ ((if t then [.label n 1 0] else []) ++ appListAppend ys) := by
    rw [Flapjack.Compiler.Backend.StackToLab.flattenHOL]
    cases t <;> simp [h1, h2, appListAppendAppend, appListAppendList]
  rw [hflat] at inst
  obtain ⟨instXs, instRest⟩ := codeInstalledAppendImp _ _ _ _ inst
  have instYs : codeInstalled (t1.pc + ((appListAppend xs).filter
      (fun x => !isLabelHOL x)).length) (appListAppend ys) t1.code := by
    cases t
    · simpa using instRest
    · simp only [if_true, List.singleton_append, codeInstalled_cons, isLabelHOL] at instRest
      exact instRest.2
  have lenFlat : ((appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL t (.seq c1 c2) n l cs bs).1).filter
      (fun x => !isLabelHOL x)).length =
      ((appListAppend xs).filter (fun x => !isLabelHOL x)).length +
        ((appListAppend ys).filter (fun x => !isLabelHOL x)).length := by
    rw [hflat]; cases t <;> simp [List.filter_append, isLabelHOL]
  rcases e1 : StackSemEvaluate.evaluate (c1, s1) with ⟨r1, s1'⟩
  rw [e1] at ev
  have lt1 : MeasureLt c1 s1 (.seq c1 c2) s1 :=
    .inr ⟨rfl, StackSemMeasure.seq_first_size_lt c1 c2⟩
  cases r1 with
  | some x =>
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    have := first false (some x) s1' n l cs bs t1
      ⟨e1, nerr, rel, ca.1, by rw [h1]; exact instXs, labs⟩
    exact boundedFlattenConcl_mono (Nat.le_add_right _ _) (boundedFlattenConclSome firstBudget this)
  | none =>
    simp only at ev
    have c1h := first false none s1' n l cs bs t1
      ⟨e1, by simp, rel, ca.1, by rw [h1]; exact instXs, labs⟩
    obtain ⟨ck, firstBound, t2, run, f1, f2, f3, f4, f5, pre, hpc, rel2⟩ := c1h
    rw [h1] at hpc
    have lt2 : MeasureLt c2 s1' (.seq c1 c2) s1 :=
      measureLtOfClockLe (StackSemEvaluateClock.evaluateClock _ _ _ _ e1)
        (StackSemMeasure.seq_second_size_lt c1 c2)
    have c2h := second s1' false r s2 n l1 cs bs t2
      (flattenHypsMid ev nerr rel2 ca.2 f1 f2 f3 f4 f5 pre
        (by rw [h2, hpc]; exact instYs) labs)
    refine boundedFlattenConclCompose firstBudget secondBudget firstBound run f1 f2 f3 f4 f5 pre ?_ c2h
    simp only [lenFlat, hpc, h2]
    omega

end
end InitECandidate.Runtime.StackToLab
#print axioms InitECandidate.Runtime.StackToLab.boundedFlattenConclCompose

#print axioms InitECandidate.Runtime.StackToLab.flattenSeq_bounded
