import InitECandidate.Runtime.StackExecutionCost
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

/-- Reached sequence work includes no suffix after a control/terminal exit. -/
theorem stackExecutionCost_seq {width : Nat} [NeZero width] {C F : Type}
    (price : HolProg width → StackSemStateFiniteExact width C F → Nat)
    (first second : HolProg width) (source : StackSemStateFiniteExact width C F) :
    stackExecutionCost price (.seq first second) source =
      price (.seq first second) source + stackExecutionCost price first source +
        (match StackSemEvaluate.evaluate (first, source) with
        | (none, middle) => stackExecutionCost price second middle
        | _ => 0) := by
  rw [stackExecutionCost, StackSemEvaluateClock.fixClockEvaluate]
  cases run : StackSemEvaluate.evaluate (first, source) with
  | mk result middle => cases result <;> rfl

/-- Local pointwise price bounds transfer along exactly the same execution,
without a factor for call depth, frame size, or program length. -/
theorem stackExecutionCost_mono {width : Nat} [NeZero width] {C F : Type}
    (small large : HolProg width → StackSemStateFiniteExact width C F → Nat)
    (le : ∀ p s, small p s ≤ large p s)
    (p : HolProg width) (s : StackSemStateFiniteExact width C F) :
    stackExecutionCost small p s ≤ stackExecutionCost large p s := by
  classical
  fun_induction stackExecutionCost small p s
  case case3 =>
    rename_i source body returned lower ihBody ihLoop
    rw [stackExecutionCost.eq_3 large source body]
    change small (.loop body) source + stackExecutionCost small body source +
      (if (StackSemControl.contLoop returned.1 && returned.2.clock != 0) = true then
        stackExecutionCost small (.loop body) (StackSemStateOps.decClock returned.2) else 0) ≤
      large (.loop body) source + stackExecutionCost large body source +
      (if (StackSemControl.contLoop returned.1 && returned.2.clock != 0) = true then
        stackExecutionCost large (.loop body) (StackSemStateOps.decClock returned.2) else 0)
    by_cases chosen : (StackSemControl.contLoop returned.1 && returned.2.clock != 0) = true
    · have recur := ihLoop chosen
      have localPrice := le (.loop body) source
      simp [chosen]
      omega
    · have localPrice := le (.loop body) source
      simp [chosen]
      omega
  all_goals (try simp_all +zetaDelta [stackExecutionCost, selectedBranchBudget, selectedContinuationBudget])
  all_goals repeat first
    | omega
    | (split <;> (try simp_all +zetaDelta only [ite_true, ite_false]))
  all_goals grind (splits := 40) only

/-- Free local nodes remain free throughout recursive execution. -/
theorem stackExecutionCost_zero {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F) :
    stackExecutionCost (fun _ _ => 0) p s = 0 := by
  classical
  fun_induction stackExecutionCost (fun _ _ => 0) p s <;>
    (try simp_all +zetaDelta [stackExecutionCost, selectedBranchBudget, selectedContinuationBudget])
  all_goals repeat first
    | omega
    | (split <;> (try simp_all +zetaDelta only [ite_true, ite_false]))
  all_goals grind (splits := 40) only

/-- Distinct local cost components add along the same actual call/loop path. -/
theorem stackExecutionCost_add {width : Nat} [NeZero width] {C F : Type}
    (left right : HolProg width → StackSemStateFiniteExact width C F → Nat)
    (p : HolProg width) (s : StackSemStateFiniteExact width C F) :
    stackExecutionCost (fun p s => left p s + right p s) p s =
      stackExecutionCost left p s + stackExecutionCost right p s := by
  classical
  fun_induction stackExecutionCost left p s
  case case3 =>
    rename_i source body returned lower ihBody ihLoop
    rw [stackExecutionCost.eq_3 (fun p s => left p s + right p s) source body,
      stackExecutionCost.eq_3 right source body]
    change left (.loop body) source + right (.loop body) source +
      stackExecutionCost (fun p s => left p s + right p s) body source +
      (if (StackSemControl.contLoop returned.1 && returned.2.clock != 0) = true then
        stackExecutionCost (fun p s => left p s + right p s) (.loop body) (StackSemStateOps.decClock returned.2) else 0) =
      (left (.loop body) source + stackExecutionCost left body source +
      (if (StackSemControl.contLoop returned.1 && returned.2.clock != 0) = true then
        stackExecutionCost left (.loop body) (StackSemStateOps.decClock returned.2) else 0)) +
      (right (.loop body) source + stackExecutionCost right body source +
      (if (StackSemControl.contLoop returned.1 && returned.2.clock != 0) = true then
        stackExecutionCost right (.loop body) (StackSemStateOps.decClock returned.2) else 0))
    by_cases chosen : (StackSemControl.contLoop returned.1 && returned.2.clock != 0) = true
    · have recur := ihLoop chosen
      simp [chosen]
      omega
    · simp [chosen]
      omega
  all_goals (try simp_all +zetaDelta [stackExecutionCost, selectedBranchBudget, selectedContinuationBudget])
  all_goals repeat first
    | omega
    | (split <;> (try simp_all +zetaDelta only [ite_true, ite_false]))
  all_goals grind (splits := 40) only

#print axioms stackExecutionCost_seq
#print axioms stackExecutionCost_mono
#print axioms stackExecutionCost_zero
#print axioms stackExecutionCost_add
end InitECandidate.Runtime.StackToLab
