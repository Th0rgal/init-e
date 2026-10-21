import InitECandidate.Runtime.StackAllocExecutedCalls

namespace InitECandidate.Runtime.StackAlloc.ExecutedCost
open Flapjack Flapjack.Compiler.Backend Flapjack.StackSemStateOps
open Flapjack.Compiler.Backend.StackLang Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend.StackProps Flapjack.StackSemMeasure
open Flapjack.Compiler.Backend.StackAlloc
open Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open InitECandidate.Runtime.StackToLab
set_option maxHeartbeats 5000000

/-- Returning-call cost under allocation lowering. The actual callee run
constructs the reached register extension; only the selected valid return or
exception continuation consumes further work. -/
theorem cost_call_some {C F : Type} (price : HolProg 64 → Nat) (anything : WordSemGcFun 64)
    (cr : CompileFn 64 C) (continuation : HolProg 64) (link l1 l2 : Nat)
    (destination : Sum Nat Nat) (handler : Option (HolProg 64 × Nat × Nat))
    (source : StackSemStateFiniteExact 64 C F)
    (free : allocationFree (.call (some (continuation, link, l1, l2)) destination handler) = true)
    (stateFree : FreeState source)
    (ih : CostIH price anything cr (.call (some (continuation, link, l1, l2)) destination handler) source) :
    CostGoal price anything cr (.call (some (continuation, link, l1, l2)) destination handler) source := by
  intro result post config regs run safe arg pre
  have continuationFree : allocationFree continuation = true := by
    rcases handler with _ | ⟨hp, h1, h2⟩ <;> simp_all [allocationFree]
  unfold StackProps.allocArg at arg
  obtain ⟨returnArg, handlerArg⟩ := arg
  replace returnArg : StackProps.allocArg continuation := returnArg
  rw [evaluate_call] at run
  dsimp only at run
  rcases found : StackSemControl.findCode destination (source.regs.eraseEq link) source.code with _ | body
  · simp only [found, Prod.mk.injEq] at run
    exact (safe run.1.symm).elim
  simp only [found] at run
  obtain ⟨key, lookup, destEq⟩ := find_code_IMP_lookup
    (find_code_regs_SUBMAP ⟨submap_domsub_both (c := link) pre.regs, found⟩)
  obtain ⟨notGC, bodyArg⟩ := pre.code key body lookup
  have bodyFree := stateFree.code key body lookup
  obtain ⟨m, n, compiledLookup⟩ := lookup_IMP_lookup_compile (c := config) ⟨lookup, notGC⟩
  have targetFound : StackSemControl.findCode destination (regs.eraseEq link)
      (sptFromAList (compile config (sptToAList source.code))) = some body := by
    rw [destEq]
    simpa only [allocationFree_comp m n body bodyFree] using compiledLookup
  by_cases zero : source.clock = 0
  · conv_lhs => rw [stackExecutionCost]
    conv_rhs => rw [stackExecutionCost]
    simp only [show (Res anything cr config source regs).clock = source.clock from rfl,
      zero, if_true, Nat.le_refl]
  rw [if_neg zero, StackSemEvaluateClock.fixClockEvaluate] at run
  let entry := decClock (StackSemStateOps.setVar link (.loc l1 l2) source)
  rcases actual : evaluate (body, entry) with ⟨bodyResult, middle⟩
  have entryRun : evaluate (body, decClock (StackSemStateOps.setVar link (.loc l1 l2) source)) =
      (bodyResult, middle) := actual
  rw [entryRun] at run
  have bodySafe : bodyResult ≠ some .error := by
    rintro rfl
    simp only [Prod.mk.injEq] at run
    exact safe run.1.symm
  have smaller : LexNat (stackSemMeasure body entry)
      (stackSemMeasure (.call (some (continuation, link, l1, l2)) destination handler) source) := by
    have positive : (StackSemStateOps.setVar link (.loc l1 l2) source).clock ≠ 0 := zero
    have h := callee_measure_lt body (.call (some (continuation, link, l1, l2)) destination handler)
      (StackSemStateOps.setVar link (.loc l1 l2) source) positive
    rwa [Zero.measure_setVar_call] at h
  have entryPre := (pre.setVar link (.loc l1 l2)).decClock
  have entryFree := (stateFree.setVar link (.loc l1 l2)).decClock
  have bodyCost := ih body entry smaller bodyFree entryFree bodyResult middle config
    (regs.updateEq (link, .loc l1 l2)) actual bodySafe bodyArg entryPre
  obtain ⟨regs1, targetRun, sub, buf, stack⟩ := Zero.allocationFree_same_clock anything cr body
    entry middle bodyResult config (regs.updateEq (link, .loc l1 l2))
    bodyFree entryFree actual bodySafe bodyArg entryPre
  have finalFree : FreeState middle := entryFree.of_evaluate actual
  have entryTarget : decClock (StackSemStateOps.setVar link (.loc l1 l2)
      (Res anything cr config source regs)) =
        Res anything cr config entry (regs.updateEq (link, .loc l1 l2)) := rfl
  have continuationSmaller : ∀ p : HolProg 64, LexNat (stackSemMeasure p middle)
      (stackSemMeasure (.call (some (continuation, link, l1, l2)) destination handler) source) := by
    intro p
    have h := call_continuation_measure_lt p (.call (some (continuation, link, l1, l2)) destination handler)
      source link l1 l2 (evaluate (body, entry)) zero
    rwa [StackSemEvaluateClock.fixClockEvaluate, actual] at h
  have nextPre : ∀ value, bodyResult = some (.result value) ∨ bodyResult = some (.exception value) →
      Pre cr config middle regs1 := by
    rintro value (rfl | rfl) <;> exact Pre.of_evaluate actual entryPre sub buf (stack (by simp))
  have selectedCost :
      selectedContinuationBudget bodyResult l1 l2 handler
          (stackExecutionCost (fun p _ => price p) continuation (Res anything cr config middle regs1))
          (match (generalizing := false) handler with
          | none => 0
          | some (hp, _, _) => stackExecutionCost (fun p _ => price p) hp (Res anything cr config middle regs1)) ≤
        selectedContinuationBudget bodyResult l1 l2 handler
          (stackExecutionCost (fun p _ => price p) continuation middle)
          (match (generalizing := false) handler with
          | none => 0
          | some (hp, _, _) => stackExecutionCost (fun p _ => price p) hp middle) := by
    rcases bodyResult with _ | outcome
    · simp only [Prod.mk.injEq] at run
      exact (safe run.1.symm).elim
    cases outcome with
    | result value =>
      dsimp only at run
      by_cases selected : value = .loc l1 l2
      · rw [if_neg (not_not.mpr selected)] at run
        have cost := ih continuation middle (continuationSmaller continuation) continuationFree finalFree
          result post config regs1 run safe returnArg (nextPre value (Or.inl rfl))
        simpa only [selectedContinuationBudget, selected, if_true] using cost
      · rw [if_pos selected] at run
        simp only [Prod.mk.injEq] at run
        exact (safe run.1.symm).elim
    | exception value =>
      dsimp only at run
      rcases handlerEq : handler with _ | ⟨hp, h1, h2⟩
      · simp only [selectedContinuationBudget, Nat.le_refl]
      · have selectedRun := run
        rw [handlerEq] at selectedRun
        dsimp only at selectedRun
        have hpFree : allocationFree hp = true := by
          have both : allocationFree continuation = true ∧ allocationFree hp = true := by
            simpa only [handlerEq, allocationFree, Bool.and_eq_true] using free
          exact both.2
        have hpArg : StackProps.allocArg hp := by simpa only [handlerEq] using handlerArg
        by_cases selected : value = .loc h1 h2
        · rw [if_neg (not_not.mpr selected)] at selectedRun
          have cost := ih hp middle (continuationSmaller hp) hpFree finalFree
            result post config regs1 selectedRun safe hpArg (nextPre value (Or.inr rfl))
          simpa only [selectedContinuationBudget, handlerEq, selected, if_true] using cost
        · rw [if_pos selected] at selectedRun
          simp only [Prod.mk.injEq] at selectedRun
          exact (safe selectedRun.1.symm).elim
    | «break» label | «continue» label =>
      simp only [Prod.mk.injEq] at run
      exact (safe run.1.symm).elim
    | error => exact (bodySafe rfl).elim
    | halt _ | timeOut | finalFFI _ => simp only [selectedContinuationBudget, Nat.le_refl]
  conv_lhs => rw [stackExecutionCost]
  conv_rhs => rw [stackExecutionCost]
  simp only [show (Res anything cr config source regs).clock = source.clock from rfl, zero, if_false,
    targetFound, found]
  rw [entryTarget]
  simp only [StackSemEvaluateClock.fixClockEvaluate]
  simp only [targetRun, entryRun]
  rcases handlerEq : handler with _ | ⟨hp, h1, h2⟩
  all_goals simp only [handlerEq] at selectedCost ⊢
  all_goals exact Nat.add_le_add_right (Nat.add_le_add bodyCost selectedCost) _

#print axioms cost_call_some
end InitECandidate.Runtime.StackAlloc.ExecutedCost
