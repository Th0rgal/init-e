import InitECandidate.Runtime.StackAllocExecutedReturn

namespace InitECandidate.Runtime.StackAlloc.ExecutedCost
open Flapjack Flapjack.Compiler.Backend Flapjack.StackSemStateOps
open Flapjack.Compiler.Backend.StackLang Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend.StackProps Flapjack.StackSemMeasure
open Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open InitECandidate.Runtime.StackToLab

/-- Whole allocation-free executed-cost transfer, by the evaluator's actual
clock/syntax measure. No recursive simulation or cost hypothesis remains. -/
theorem cost_all {C F : Type} (price : HolProg 64 → Nat) (anything : WordSemGcFun 64)
    (cr : CompileFn 64 C) :
    ∀ (measure : Nat × Nat) (program : HolProg 64) (source : StackSemStateFiniteExact 64 C F),
      stackSemMeasure program source = measure → allocationFree program = true → FreeState source →
      CostGoal price anything cr program source := by
  intro measure
  induction measure using EvaluateAddClock.lexNat_wf.induction with
  | _ measure ih =>
    intro program source same free stateFree
    subst same
    have smaller : CostIH price anything cr program source := by
      intro child state lt childFree childStateFree
      exact ih _ lt child state rfl childFree childStateFree
    cases program
    case seq first second => exact cost_seq price anything cr first second source free stateFree smaller
    case ite cmp reg operand first second =>
      exact cost_ite price anything cr cmp reg operand first second source free stateFree smaller
    case loop body => exact cost_loop price anything cr body source free stateFree smaller
    case jumpLower first second destination =>
      exact cost_jumpLower price anything cr first second destination source stateFree smaller
    case rawCall destination => exact cost_rawCall price anything cr destination source stateFree smaller
    case call returns destination handler =>
      rcases returns with _ | ⟨continuation, link, l1, l2⟩
      · rcases handler with _ | ⟨hp, h1, h2⟩
        · exact cost_call_none price anything cr destination source stateFree smaller
        · simp only [allocationFree, Bool.false_eq_true] at free
      · exact cost_call_some price anything cr continuation link l1 l2 destination handler source free stateFree smaller
    all_goals
      apply cost_atomic
      rfl

/-- Allocation lowering preserves both the actual run and its executed cost
for certified code. This strengthens the older zero-extra-clock result; it
retains all original state and postcondition requirements. -/
theorem allocationFree_executed_cost {C F : Type} (price : HolProg 64 → Nat)
    (anything : WordSemGcFun 64) (cr : CompileFn 64 C) (program : HolProg 64)
    (source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))
    (config : DataToWord.Config) (regs : HolFiniteMapExact Nat (WordLocW 64))
    (free : allocationFree program = true) (stateFree : FreeState source)
    (run : evaluate (program, source) = (result, post)) (safe : result ≠ some .error)
    (arg : StackProps.allocArg program) (pre : Pre cr config source regs) :
    ∃ regs1,
      evaluate (program, Res anything cr config source regs) =
        (result, Res anything cr config post regs1) ∧ Post result post regs1 ∧
      stackExecutionCost (fun p _ => price p) program (Res anything cr config source regs) ≤
        stackExecutionCost (fun p _ => price p) program source := by
  obtain ⟨regs1, targetRun, related⟩ := Zero.allocationFree_same_clock anything cr program source post result
    config regs free stateFree run safe arg pre
  exact ⟨regs1, targetRun, related,
    cost_all price anything cr _ program source rfl free stateFree result post config regs run safe arg pre⟩

#print axioms cost_all
#print axioms allocationFree_executed_cost
end InitECandidate.Runtime.StackAlloc.ExecutedCost
