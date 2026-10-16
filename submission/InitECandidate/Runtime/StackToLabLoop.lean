import InitECandidate.Runtime.StackToLabCompose
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.Loop

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
/-- The body's continuation reaches the back jump with the state relation. -/
theorem boundedLoopReentry {body : HolProg width} {s1' : StackSemStateFiniteExact width C F}
    {res : Option (StackSemResult width)} {n l l1 : Nat} {cs bs : List Nat}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F}
    {xs : AppList (LabLineHOL width)} {nr : Bool}
    (h1 : Flapjack.Compiler.Backend.StackToLab.flattenHOL false body n (l + 2) (l :: cs) ((l + 1) :: bs) = (xs, nr, l1))
    (fetchJ : asmFetchAux (t1.pc + ((appListAppend xs).filter (fun x => !isLabelHOL x)).length)
      t1.code = some (.labAsm (.jump (.lab n l)) 0 [] 0))
    (hc : StackSemControl.contLoop res = true)
    (budget : Nat)
    (bh : BoundedFlattenConcl body false res s1' n (l + 2) (l :: cs) ((l + 1) :: bs) t1 budget) :
    ∃ (ck : Nat), ck ≤ budget ∧ ∃ (t2 : Flapjack.Compiler.Backend.LabSem.State width C F),
      (∀ ck1, evaluate { t1 with clock := t1.clock + ck + ck1 } =
        evaluate { t2 with clock := t2.clock + ck1 }) ∧
      t2.lenReg = t1.lenReg ∧ t2.ptrReg = t1.ptrReg ∧ t2.len2Reg = t1.len2Reg ∧
      t2.ptr2Reg = t1.ptr2Reg ∧ t2.linkReg = t1.linkReg ∧ t1.code <+: t2.code ∧
      stateRel s1' t2 ∧ asmFetchAux t2.pc t2.code = some (.labAsm (.jump (.lab n l)) 0 [] 0) := by
  cases res with
  | none =>
    obtain ⟨ck, bound, t2, run, f1, f2, f3, f4, f5, pre, hpc, rel2⟩ := bh
    rw [h1] at hpc
    exact ⟨ck, bound, t2, run, f1, f2, f3, f4, f5, pre, rel2, by
      rw [hpc]; exact asmFetchAuxSomeIsPrefix _ _ _ _ ⟨fetchJ, pre⟩⟩
  | some x =>
    rcases x with _ | _ | _ | k | _ | _ | _ | _
    case «continue» =>
      simp only [StackSemControl.contLoop, decide_eq_true_eq] at hc
      subst hc
      obtain ⟨ck, bound, t2, h⟩ := bh
      simp only [haltView, Option.map_some, resultView, Flapjack.Compiler.Backend.StackToLab.findLabHOL,
        List.getElem?_cons_zero, Option.getD_some] at h
      obtain ⟨run, f1, f2, f3, f4, f5, pre, rel2, inst2⟩ := h
      exact ⟨ck, bound, t2, run, f1, f2, f3, f4, f5, pre, rel2, fetchSingle rfl inst2⟩
    all_goals simp [StackSemControl.contLoop] at hc

/-- Results with the same halt view and result view have the same
conclusion, for any program, label stacks and next label. -/
theorem boundedFlattenConclResult {p p' : HolProg width} {t t' : Bool} {x y : StackSemResult width}
    {s2 : StackSemStateFiniteExact width C F} {n n' l l' : Nat} {cs bs cs' bs' : List Nat}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (hh : haltView (some x) = haltView (some y))
    (hr : resultView x n cs bs = resultView y n' cs' bs')
    (budget : Nat)
    (h : BoundedFlattenConcl p t (some x) s2 n l cs bs t1 budget) :
    BoundedFlattenConcl p' t' (some y) s2 n' l' cs' bs' t1 budget := by
  obtain ⟨ck, bound, t2, h⟩ := h
  refine ⟨ck, bound, t2, ?_⟩
  revert h
  rw [hh]
  cases haltView (some y) with
  | some res => exact id
  | none =>
    simp only [Option.map_some, hr]
    cases resultView y n' cs' bs' <;> exact id


/-- `Loop` case. -/
theorem flattenLoop_bounded (s1 : StackSemStateFiniteExact width C F) (body : HolProg width)
    (budget : Nat)
    (first : ∀ (middle : StackSemStateFiniteExact width C F), BoundedFlattenProp body middle budget) :
    BoundedFlattenProp (.loop body) s1 (budget * (s1.clock + 1)) := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, ca, inst, labs⟩
  rw [StackSemEvaluate.evaluate_loop, StackSemEvaluateClock.fixClockEvaluate] at ev
  simp only [Flapjack.Compiler.Backend.StackProps.callArgs] at ca
  have tf : Flapjack.Compiler.Backend.StackToLab.flattenHOL t (.loop body) n l cs bs = Flapjack.Compiler.Backend.StackToLab.flattenHOL false (.loop body) n l cs bs := by
    cases t
    · rfl
    · exact flattenTF (by simp [Flapjack.Compiler.Backend.StackToLab.isSeqHOL])
  rcases h1 : Flapjack.Compiler.Backend.StackToLab.flattenHOL false body n (l + 2) (l :: cs) ((l + 1) :: bs) with ⟨xs, nr1, l1⟩
  have hflat : appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL t (.loop body) n l cs bs).1 =
      .label n l 0 :: (appListAppend xs ++
        [.labAsm (.jump (.lab n l)) 0 [] 0, .label n (l + 1) 0]) := by
    rw [tf, Flapjack.Compiler.Backend.StackToLab.flattenHOL]; simp [h1, appListAppendAppend, appListAppendList]
  have total : ((appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL t (.loop body) n l cs bs).1).filter
      (fun x => !isLabelHOL x)).length =
      ((appListAppend xs).filter (fun x => !isLabelHOL x)).length + 1 := by
    rw [hflat]; simp [List.filter_append, isLabelHOL]
  have inst0 := inst
  rw [hflat] at inst
  obtain ⟨locL, inst1⟩ := labelAt inst
  obtain ⟨instXs, instRest⟩ := codeInstalledAppendImp _ _ _ _ inst1
  obtain ⟨fetchJ, instRest2⟩ := lineAt rfl instRest
  obtain ⟨locL1, -⟩ := labelAt instRest2
  rcases e1 : StackSemEvaluate.evaluate (body, s1) with ⟨res, s1'⟩
  rw [e1] at ev
  simp only at ev
  have lt1 : MeasureLt body s1 (.loop body) s1 :=
    .inr ⟨rfl, StackSemMeasure.loop_body_size_lt body⟩
  have labs' : ∀ k ∈ (l :: cs) ++ ((l + 1) :: bs) ++ [0], (locToPc n k t1.code).isSome := by
    intro k hk
    by_cases e : k = l
    · subst e; simp [locL]
    by_cases e' : k = l + 1
    · subst e'; simp [locL1]
    apply labs k
    simp only [List.cons_append, List.mem_cons, List.mem_append] at hk ⊢
    tauto
  have nerrBody : res ≠ some .error := by
    rintro rfl
    simp [StackSemControl.contLoop, StackSemControl.exitLoop] at ev
    exact nerr ev.1.symm
  have bh := first s1 false res s1' n (l + 2) (l :: cs) ((l + 1) :: bs) t1
    ⟨e1, nerrBody, rel, ca, by rw [h1]; exact instXs, labs'⟩
  by_cases hc : StackSemControl.contLoop res = true
  · rw [if_pos hc] at ev
    obtain ⟨ck, bound, t2, run, f1, f2, f3, f4, f5, pre, rel2, fetch2⟩ := boundedLoopReentry h1 fetchJ hc budget bh
    split_ifs at ev with hz
    · simp only [Prod.mk.injEq] at ev
      obtain ⟨rfl, rfl⟩ := ev
      refine ⟨ck, by
        have m := Nat.mul_le_mul_left budget (Nat.succ_pos s1.clock)
        exact bound.trans (by simpa using m), t2, run, f1, f2, f3, f4, f5, pre, ?_, ?_⟩
      · simp [StackSemStateOps.emptyEnv, relFfi rel2]
      · rw [relClock rel2]; exact hz
    · have clk2 : t2.clock ≠ 0 := by rw [relClock rel2]; exact hz
      have lt2 : MeasureLt (.loop body) (StackSemStateOps.decClock s1') (.loop body) s1 := by
        left
        have := StackSemEvaluateClock.evaluateClock _ _ _ _ e1
        simp only [StackSemStateOps.decClock]
        omega
      have locL2 := locToPcIsPrefix _ _ _ _ _ ⟨locL, pre⟩
      have rel3 : stateRel (StackSemStateOps.decClock s1')
          { t2 with pc := t1.pc, clock := t2.clock - 1 } := StateRel.stateRelDecClock rel2
      have lh := flattenLoop_bounded (StackSemStateOps.decClock s1') body budget first t r s2 n l cs bs
        { t2 with pc := t1.pc, clock := t2.clock - 1 }
        ⟨ev, nerr, rel3, by rw [f1, f2, f3, f4, f5]; exact ca,
          codeInstalledIsPrefix _ _ _ _ ⟨inst0, pre⟩,
          fun k hk => isSomeLocToPcPrefix ⟨labs k hk, pre⟩⟩
      have smaller : (StackSemStateOps.decClock s1').clock + 1 ≤ s1.clock := by
        have clockLe := StackSemEvaluateClock.evaluateClock _ _ _ _ e1
        simp only [StackSemStateOps.decClock]
        omega
      have totalBound : budget + budget * ((StackSemStateOps.decClock s1').clock + 1) ≤
          budget * (s1.clock + 1) := by
        have m := Nat.mul_le_mul_left budget smaller
        calc
          budget + budget * ((StackSemStateOps.decClock s1').clock + 1) ≤
              budget + budget * s1.clock := Nat.add_le_add_left m budget
          _ = budget * (s1.clock + 1) := by simp [Nat.mul_add, Nat.add_comm]
      apply boundedFlattenConcl_mono totalBound
      refine boundedFlattenConclCompose (ck := ck) (t2 := { t2 with pc := t1.pc, clock := t2.clock - 1 })
        budget (budget * ((StackSemStateOps.decClock s1').clock + 1)) bound
        (fun ck1 => ?_) f1 f2 f3 f4 f5 pre rfl lh
      rw [run, show t2.clock + ck1 = (t2.clock - 1 + ck1) + 1 by omega,
        jumpStep (t2.clock - 1 + ck1) fetch2 locL2]
  · rw [if_neg hc] at ev
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    rcases res with _ | x
    · simp [StackSemControl.contLoop] at hc
    rcases x with v | v | k | k | v | _ | o | _
    · exact boundedFlattenConcl_mono (Nat.le_mul_of_pos_right budget (Nat.succ_pos _)) (boundedFlattenConclResult (h := bh) (budget := budget) rfl (by cases v <;> rfl))
    · exact boundedFlattenConcl_mono (Nat.le_mul_of_pos_right budget (Nat.succ_pos _)) (boundedFlattenConclResult (h := bh) (budget := budget) rfl (by cases v <;> rfl))
    · -- `Break k`
      rcases k with _ | k
      · -- `Break 0` leaves the loop after the break label
        simp only [StackSemControl.exitLoop, if_true]
        obtain ⟨ck, bound, t2, h⟩ := bh
        simp only [haltView, Option.map_some, resultView, Flapjack.Compiler.Backend.StackToLab.findLabHOL,
          List.getElem?_cons_zero, Option.getD_some] at h
        obtain ⟨run, f1, f2, f3, f4, f5, pre, -, hw⟩ := h
        obtain ⟨hpc, rel2⟩ := hw _ (locToPcIsPrefix _ _ _ _ _ ⟨locL1, pre⟩)
        refine ⟨ck, by
        have m := Nat.mul_le_mul_left budget (Nat.succ_pos s1.clock)
        exact bound.trans (by simpa using m), t2, run, f1, f2, f3, f4, f5, pre, ?_, rel2⟩
        rw [← hpc, total]
        omega
      · simp only [StackSemControl.exitLoop, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
        refine boundedFlattenConcl_mono (Nat.le_mul_of_pos_right budget (Nat.succ_pos _)) (boundedFlattenConclResult (h := bh) (budget := budget) (by simp [haltView]) ?_)
        simp [resultView, Flapjack.Compiler.Backend.StackToLab.findLabHOL]
    · -- `Continue k`, `k ≠ 0`
      rcases k with _ | k
      · simp [StackSemControl.contLoop] at hc
      · simp only [StackSemControl.exitLoop, Nat.add_sub_cancel]
        refine boundedFlattenConcl_mono (Nat.le_mul_of_pos_right budget (Nat.succ_pos _)) (boundedFlattenConclResult (h := bh) (budget := budget) (by simp [haltView]) ?_)
        simp [resultView, Flapjack.Compiler.Backend.StackToLab.findLabHOL]
    all_goals exact boundedFlattenConcl_mono (Nat.le_mul_of_pos_right budget (Nat.succ_pos _)) (boundedFlattenConclResult (h := bh) (budget := budget) rfl (by simp [resultView]))
termination_by s1.clock
decreasing_by
  have h := StackSemEvaluateClock.evaluateClock _ _ _ _ e1
  simp only [StackSemStateOps.decClock]
  omega

end
end InitECandidate.Runtime.StackToLab
#print axioms InitECandidate.Runtime.StackToLab.flattenLoop_bounded
