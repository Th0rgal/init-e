import InitECandidate.Runtime.StackAllocZeroCorrect
import InitECandidate.Runtime.StackExecutionCostProps

namespace InitECandidate.Runtime.StackAlloc.ExecutedCost
open Flapjack Flapjack.Compiler.Backend Flapjack.StackSemStateOps
open Flapjack.Compiler.Backend.StackLang Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend.StackProps Flapjack.StackSemMeasure
open Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open InitECandidate.Runtime.StackToLab
set_option maxHeartbeats 4000000

/-- Allocation-free lowering must preserve executed work as well as semantic
clock. Prices depend on the emitted node, not on simulation bookkeeping. -/
def CostGoal {C F : Type} (price : HolProg 64 → Nat) (anything : WordSemGcFun 64)
    (cr : CompileFn 64 C) (program : HolProg 64) (source : StackSemStateFiniteExact 64 C F) : Prop :=
  ∀ (result : Option (StackSemResult 64)) (post : StackSemStateFiniteExact 64 C F)
    (config : DataToWord.Config) (regs : HolFiniteMapExact Nat (WordLocW 64)),
    evaluate (program, source) = (result, post) → result ≠ some .error →
    StackProps.allocArg program → Pre cr config source regs →
    stackExecutionCost (fun p _ => price p) program (Res anything cr config source regs) ≤
      stackExecutionCost (fun p _ => price p) program source

abbrev CostIH {C F : Type} (price : HolProg 64 → Nat) (anything : WordSemGcFun 64)
    (cr : CompileFn 64 C) (program : HolProg 64) (source : StackSemStateFiniteExact 64 C F) : Prop :=
  ∀ (child : HolProg 64) (state : StackSemStateFiniteExact 64 C F),
    LexNat (stackSemMeasure child state) (stackSemMeasure program source) →
    allocationFree child = true → FreeState state → CostGoal price anything cr child state

def costAtomic : HolProg 64 → Bool
  | .seq _ _ | .ite _ _ _ _ _ | .loop _ | .jumpLower _ _ _ | .rawCall _ | .call _ _ _ => false
  | _ => true

/-- Every atomic node has identical local price on the two simulation states. -/
theorem cost_atomic {C F : Type} (price : HolProg 64 → Nat) (anything : WordSemGcFun 64)
    (cr : CompileFn 64 C) (program : HolProg 64) (source : StackSemStateFiniteExact 64 C F)
    (leaf : costAtomic program = true) : CostGoal price anything cr program source := by
  intro result post config regs run safe arg pre
  cases program <;> simp_all only [costAtomic, Bool.false_eq_true, stackExecutionCost, Nat.le_refl]

/-- Sequence transport follows the actual source prefix. The existing
allocation simulation constructs its target prefix and supplies the full
postcondition needed for the selected suffix's cost induction. -/
theorem cost_seq {C F : Type} (price : HolProg 64 → Nat) (anything : WordSemGcFun 64)
    (cr : CompileFn 64 C) (first second : HolProg 64) (source : StackSemStateFiniteExact 64 C F)
    (free : allocationFree (.seq first second) = true) (stateFree : FreeState source)
    (ih : CostIH price anything cr (.seq first second) source) :
    CostGoal price anything cr (.seq first second) source := by
  have parts : allocationFree first = true ∧ allocationFree second = true := by
    simpa only [allocationFree, Bool.and_eq_true] using free
  intro result post config regs run safe arg pre
  obtain ⟨argFirst, argSecond⟩ := arg
  rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate] at run
  rcases actual : evaluate (first, source) with ⟨middleResult, middle⟩
  rw [actual] at run
  have firstSafe : middleResult ≠ some .error := by
    rintro rfl
    simp only [Prod.mk.injEq] at run
    exact safe run.1.symm
  have firstCost := ih first source (seq_first_measure_lt first second source) parts.1 stateFree
    middleResult middle config regs actual firstSafe argFirst pre
  obtain ⟨regs1, targetRun, sub, buf, stack⟩ := Zero.allocationFree_same_clock anything cr first
    source middle middleResult config regs parts.1 stateFree actual firstSafe argFirst pre
  cases middleResult with
  | some outcome =>
    rw [stackExecutionCost_seq, stackExecutionCost_seq, targetRun, actual]
    simp only [Nat.add_zero]
    exact Nat.add_le_add_left firstCost _
  | none =>
    have smaller := seq_second_measure_lt first second source (evaluate (first, source))
    rw [StackSemEvaluateClock.fixClockEvaluate, actual] at smaller
    have nextPre := Pre.of_evaluate actual pre sub buf (stack (by simp))
    have nextCost := ih second middle smaller parts.2 (stateFree.of_evaluate actual)
      result post config regs1 run safe argSecond nextPre
    rw [stackExecutionCost_seq, stackExecutionCost_seq, targetRun, actual]
    exact Nat.add_le_add (Nat.add_le_add_left firstCost _) nextCost

/-- Conditional transport uses the operand values present in the source.
The register-submap invariant preserves those values in the actual target;
no bound on the unselected arm is charged. -/
theorem cost_ite {C F : Type} (price : HolProg 64 → Nat) (anything : WordSemGcFun 64)
    (cr : CompileFn 64 C) (cmp : Compiler.Encoders.Asm.HolCmp) (reg : Nat)
    (operand : Compiler.Encoders.Asm.HolRegImm 64) (first second : HolProg 64)
    (source : StackSemStateFiniteExact 64 C F)
    (free : allocationFree (.ite cmp reg operand first second) = true) (stateFree : FreeState source)
    (ih : CostIH price anything cr (.ite cmp reg operand first second) source) :
    CostGoal price anything cr (.ite cmp reg operand first second) source := by
  have parts : allocationFree first = true ∧ allocationFree second = true := by
    simpa only [allocationFree, Bool.and_eq_true] using free
  intro result post config regs run safe arg pre
  obtain ⟨argFirst, argSecond⟩ := arg
  rw [evaluate_ite] at run
  split at run
  · rename_i x y hx hy
    have tx := getVar_res anything cr config source regs pre.regs hx
    have ty := Zero.getVarImm_res anything cr config source regs pre.regs operand hy
    split at run
    · rename_i selected
      have chosen := ih first source (if_first_measure_lt cmp reg operand first second source)
        parts.1 stateFree result post config regs run safe argFirst pre
      rw [stackExecutionCost, stackExecutionCost]
      simp only [selectedBranchBudget, hx, hy, tx, ty, selected]
      exact Nat.add_le_add_left chosen _
    · rename_i selected
      have chosen := ih second source (if_second_measure_lt cmp reg operand first second source)
        parts.2 stateFree result post config regs run safe argSecond pre
      rw [stackExecutionCost, stackExecutionCost]
      simp only [selectedBranchBudget, hx, hy, tx, ty, selected]
      exact Nat.add_le_add_left chosen _
    · simp only [Prod.mk.injEq] at run
      exact (safe run.1.symm).elim
  · simp only [Prod.mk.injEq] at run
    exact (safe run.1.symm).elim

/-- Loop cost transport charges each actual body once and recurses only when
that body continues with a positive clock. Semantic prefix simulation aligns
the target's reached register extension with the recursive cost proof. -/
theorem cost_loop {C F : Type} (price : HolProg 64 → Nat) (anything : WordSemGcFun 64)
    (cr : CompileFn 64 C) (body : HolProg 64) (source : StackSemStateFiniteExact 64 C F)
    (free : allocationFree (.loop body) = true) (stateFree : FreeState source)
    (ih : CostIH price anything cr (.loop body) source) :
    CostGoal price anything cr (.loop body) source := by
  have bodyFree : allocationFree body = true := by simpa only [allocationFree] using free
  intro result post config regs run safe arg pre
  rw [evaluate_loop, StackSemEvaluateClock.fixClockEvaluate] at run
  rcases actual : evaluate (body, source) with ⟨middleResult, middle⟩
  rw [actual] at run
  dsimp only at run
  have bodySafe : middleResult ≠ some .error := by
    rintro rfl
    simp only [StackSemControl.contLoop, StackSemControl.exitLoop, Bool.false_eq_true, if_false,
      Prod.mk.injEq] at run
    exact safe run.1.symm
  have bodyCost := ih body source (loop_body_measure_lt body source) bodyFree stateFree
    middleResult middle config regs actual bodySafe arg pre
  obtain ⟨regs1, targetRun, sub, buf, stack⟩ := Zero.allocationFree_same_clock anything cr body
    source middle middleResult config regs bodyFree stateFree actual bodySafe arg pre
  conv_lhs => rw [stackExecutionCost]
  conv_rhs => rw [stackExecutionCost]
  simp only [StackSemEvaluateClock.fixClockEvaluate]
  simp only [targetRun, actual]
  by_cases continuing : StackSemControl.contLoop middleResult = true
  · have nonhalt : ∀ w, middleResult ≠ some (.halt w) := by
      rcases contLoopImp middleResult continuing with rfl | rfl <;> simp
    rw [if_pos continuing] at run
    by_cases exhausted : middle.clock = 0
    · simp only [continuing, Bool.true_and]
      simp only [show (Res anything cr config middle regs1).clock = middle.clock from rfl,
        exhausted, show ((0 : Nat) != 0) = false from rfl, Bool.false_eq_true, if_false, Nat.add_zero]
      exact Nat.add_le_add_left bodyCost _
    · rw [if_neg exhausted] at run
      have smaller := loop_reentry_measure_lt body source (evaluate (body, source))
      rw [StackSemEvaluateClock.fixClockEvaluate, actual] at smaller
      have nextPre := (Pre.of_evaluate actual pre sub buf (stack nonhalt)).decClock
      have nextCost := ih (.loop body) (decClock middle) (smaller exhausted) free
        (stateFree.of_evaluate actual).decClock result post config regs1 run safe arg nextPre
      simp only [continuing, Bool.true_and,
        show (Res anything cr config middle regs1).clock = middle.clock from rfl]
      have positive : (middle.clock != 0) = true := by simpa using exhausted
      simp only [positive, if_true]
      exact Nat.add_le_add (Nat.add_le_add_left bodyCost _) nextCost
  · have stopped : StackSemControl.contLoop middleResult = false := by simpa using continuing
    simp only [stopped, Bool.false_and, Bool.false_eq_true, if_false, Nat.add_zero]
    exact Nat.add_le_add_left bodyCost _


#print axioms cost_atomic
#print axioms cost_seq
#print axioms cost_ite
#print axioms cost_loop
end InitECandidate.Runtime.StackAlloc.ExecutedCost
