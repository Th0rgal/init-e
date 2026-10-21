import InitECandidate.Runtime.StackAllocExecutedCost

namespace InitECandidate.Runtime.StackAlloc.ExecutedCost
open Flapjack Flapjack.Compiler.Backend Flapjack.StackSemStateOps
open Flapjack.Compiler.Backend.StackLang Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend.StackProps Flapjack.StackSemMeasure
open Flapjack.Compiler.Backend.StackAlloc
open Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open InitECandidate.Runtime.StackToLab
set_option maxHeartbeats 4000000

/-- Direct and indirect tail calls preserve their actual executed callee
price. Code lookup is derived through the compiler's concrete stub/map
construction; syntax identity follows from the allocation-free certificate. -/
theorem cost_call_none {C F : Type} (price : HolProg 64 → Nat) (anything : WordSemGcFun 64)
    (cr : CompileFn 64 C) (destination : Sum Nat Nat) (source : StackSemStateFiniteExact 64 C F)
    (stateFree : FreeState source)
    (ih : CostIH price anything cr (.call none destination none) source) :
    CostGoal price anything cr (.call none destination none) source := by
  intro result post config regs run safe arg pre
  rw [evaluate_call] at run
  dsimp only at run
  rcases found : StackSemControl.findCode destination source.regs source.code with _ | body
  · simp only [found, Prod.mk.injEq] at run
    exact (safe run.1.symm).elim
  simp only [found] at run
  obtain ⟨key, lookup, destEq⟩ := find_code_IMP_lookup (find_code_regs_SUBMAP ⟨pre.regs, found⟩)
  obtain ⟨notGC, bodyArg⟩ := pre.code key body lookup
  have bodyFree := stateFree.code key body lookup
  obtain ⟨m, n, compiledLookup⟩ := lookup_IMP_lookup_compile (c := config) ⟨lookup, notGC⟩
  have targetFound : StackSemControl.findCode destination regs
      (sptFromAList (compile config (sptToAList source.code))) = some body := by
    rw [destEq]
    simpa only [allocationFree_comp m n body bodyFree] using compiledLookup
  by_cases zero : source.clock = 0
  · conv_lhs => rw [stackExecutionCost]
    conv_rhs => rw [stackExecutionCost]
    simp only [Option.isSome_none, Bool.false_eq_true, if_false,
      show (Res anything cr config source regs).clock = source.clock from rfl,
      zero, if_true, Nat.le_refl]
  · rw [if_neg zero, StackSemEvaluateClock.fixClockEvaluate] at run
    rcases actual : evaluate (body, decClock source) with ⟨bodyResult, bodyPost⟩
    rw [actual] at run
    dsimp only at run
    have bodySafe : bodyResult ≠ some .error := by
      rintro rfl
      simp only [StackSemControl.badFunReturn, Bool.false_eq_true, if_false, Prod.mk.injEq] at run
      exact safe run.1.symm
    have bodyCost := ih body (decClock source) (callee_measure_lt body _ source zero)
      bodyFree stateFree.decClock bodyResult bodyPost config regs actual bodySafe bodyArg pre.decClock
    conv_lhs => rw [stackExecutionCost]
    conv_rhs => rw [stackExecutionCost]
    simp only [Option.isSome_none, Bool.false_eq_true, if_false,
      show (Res anything cr config source regs).clock = source.clock from rfl, zero,
      targetFound, found]
    exact Nat.add_le_add_left bodyCost _

/-- Raw calls enter after the certified prologue. Allocation-free compilation
preserves that actual sequence shape as well as the selected suffix's cost. -/
theorem cost_rawCall {C F : Type} (price : HolProg 64 → Nat) (anything : WordSemGcFun 64)
    (cr : CompileFn 64 C) (destination : Nat) (source : StackSemStateFiniteExact 64 C F)
    (stateFree : FreeState source)
    (ih : CostIH price anything cr (.rawCall destination) source) :
    CostGoal price anything cr (.rawCall destination) source := by
  intro result post config regs run safe arg pre
  rw [evaluate_rawCall] at run
  split at run
  · simp only [Prod.mk.injEq] at run
    exact (safe run.1.symm).elim
  rename_i program found
  obtain ⟨notGC, programArg⟩ := pre.code destination program found
  have programFree := stateFree.code destination program found
  obtain ⟨m, n, compiledLookup⟩ := lookup_IMP_lookup_compile (c := config) ⟨found, notGC⟩
  have targetLookup : sptLookup destination (Res anything cr config source regs).code = some program := by
    simpa only [allocationFree_comp m n program programFree] using compiledLookup
  split at run
  · rename_i prologue body shape
    cases program with
    | seq first second =>
      simp only [StackSemControl.destSeq, Option.some.injEq, Prod.mk.injEq] at shape
      obtain ⟨rfl, rfl⟩ := shape
      have freeParts : allocationFree first = true ∧ allocationFree second = true := by
        simpa only [allocationFree, Bool.and_eq_true] using programFree
      by_cases zero : source.clock = 0
      · conv_lhs => rw [stackExecutionCost]
        conv_rhs => rw [stackExecutionCost]
        simp only [show (Res anything cr config source regs).clock = source.clock from rfl,
          zero, if_true, Nat.le_refl]
      · rw [if_neg zero] at run
        rcases actual : evaluate (second, decClock source) with ⟨bodyResult, bodyPost⟩
        rw [actual] at run
        dsimp only at run
        have bodySafe : bodyResult ≠ some .error := by
          rintro rfl
          simp only [StackSemControl.badFunReturn, Bool.false_eq_true, if_false, Prod.mk.injEq] at run
          exact safe run.1.symm
        have bodyCost := ih second (decClock source) (callee_measure_lt second _ source zero)
          freeParts.2 stateFree.decClock bodyResult bodyPost config regs actual bodySafe programArg.2 pre.decClock
        conv_lhs => rw [stackExecutionCost]
        conv_rhs => rw [stackExecutionCost]
        simp only [show (Res anything cr config source regs).clock = source.clock from rfl,
          zero, if_false, targetLookup, found]
        exact Nat.add_le_add_left bodyCost _
    | _ => simp [StackSemControl.destSeq] at shape
  · simp only [Prod.mk.injEq] at run
    exact (safe run.1.symm).elim


/-- Conditional jumps use the preserved source word operands and the actual
compiled-table lookup; an untaken jump charges no callee execution. -/
theorem cost_jumpLower {C F : Type} (price : HolProg 64 → Nat) (anything : WordSemGcFun 64)
    (cr : CompileFn 64 C) (first second destination : Nat) (source : StackSemStateFiniteExact 64 C F)
    (stateFree : FreeState source)
    (ih : CostIH price anything cr (.jumpLower first second destination) source) :
    CostGoal price anything cr (.jumpLower first second destination) source := by
  intro result post config regs run safe arg pre
  rw [evaluate_jumpLower] at run
  split at run
  · rename_i x y hx hy
    have tx := getVar_res anything cr config source regs pre.regs hx
    have ty := getVar_res anything cr config source regs pre.regs hy
    split at run
    · rename_i selected
      split at run
      · simp only [Prod.mk.injEq] at run
        exact (safe run.1.symm).elim
      rename_i body found
      have lookup : sptLookup destination source.code = some body := found
      obtain ⟨notGC, bodyArg⟩ := pre.code destination body lookup
      have bodyFree := stateFree.code destination body lookup
      obtain ⟨m, n, compiledLookup⟩ := lookup_IMP_lookup_compile (c := config) ⟨lookup, notGC⟩
      have targetFound : StackSemControl.findCode (.inl destination) regs
          (Res anything cr config source regs).code = some body := by
        simpa only [StackSemControl.findCode, allocationFree_comp m n body bodyFree] using compiledLookup
      by_cases zero : source.clock = 0
      · conv_lhs => rw [stackExecutionCost]
        conv_rhs => rw [stackExecutionCost]
        simp only [hx, hy, tx, ty, selected, if_true,
          show (Res anything cr config source regs).clock = source.clock from rfl, zero, Nat.le_refl]
      · rw [if_neg zero] at run
        rcases actual : evaluate (body, decClock source) with ⟨bodyResult, bodyPost⟩
        rw [actual] at run
        dsimp only at run
        have bodySafe : bodyResult ≠ some .error := by
          rintro rfl
          simp only [StackSemControl.badFunReturn, Bool.false_eq_true, if_false, Prod.mk.injEq] at run
          exact safe run.1.symm
        have bodyCost := ih body (decClock source) (callee_measure_lt body _ source zero)
          bodyFree stateFree.decClock bodyResult bodyPost config regs actual bodySafe bodyArg pre.decClock
        conv_lhs => rw [stackExecutionCost]
        conv_rhs => rw [stackExecutionCost]
        simp only [hx, hy, tx, ty, selected, if_true,
          show (Res anything cr config source regs).clock = source.clock from rfl,
          zero, if_false, targetFound, found]
        exact Nat.add_le_add_left bodyCost _
    · rename_i unselected
      conv_lhs => rw [stackExecutionCost]
      conv_rhs => rw [stackExecutionCost]
      simp only [hx, hy, tx, ty, unselected, Bool.false_eq_true, if_false, Nat.le_refl]
  · simp only [Prod.mk.injEq] at run
    exact (safe run.1.symm).elim


#print axioms cost_call_none
#print axioms cost_rawCall
#print axioms cost_jumpLower
end InitECandidate.Runtime.StackAlloc.ExecutedCost
