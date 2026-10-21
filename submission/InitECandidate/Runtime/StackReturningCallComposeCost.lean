import InitECandidate.Runtime.StackReturningCallRunCost
import InitECandidate.Runtime.StackExecutionCostAddClock
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target

variable {price : HolProg 64 → Nat} [caps : ConservativeRemovalPrice price]

/-- Extending a completed callee's clock for its continuation preserves the
callee's actual cost. The two reached budgets add with one local call charge. -/
theorem stackCost_returning_call_composeSelected {F : Type}
    (callee continuation : HolProg 64) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (handler : Option (HolProg 64 × Nat × Nat)) (result : Option (StackSemResult 64))
    (source post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (bodyClock continuationClock bodyBudget continuationBudget : Nat)
    (nonzero : source.clock ≠ 0)
    (found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some callee)
    (run : StackSemEvaluate.evaluate
      (callee, {StackSemStateOps.setVar link (.loc l1 l2) (StackSemStateOps.decClock source) with
        clock := (StackSemStateOps.decClock source).clock + bodyClock}) =
      (result, post))
    (notTimeout : result ≠ some .timeOut)
    (bodyCost : stackExecutionCost (fun p _ => price p)
      callee {StackSemStateOps.setVar link (.loc l1 l2) (StackSemStateOps.decClock source) with
        clock := (StackSemStateOps.decClock source).clock + bodyClock} ≤ bodyBudget)
    (continuationCost : selectedContinuationBudget result l1 l2 handler
      (stackExecutionCost (fun p _ => price p) continuation {post with clock := post.clock+continuationClock})
      (match handler with
       | none => 0
       | some (body,_,_) => stackExecutionCost (fun p _ => price p) body {post with clock := post.clock+continuationClock}) ≤
      continuationBudget) :
    stackExecutionCost (fun p _ => price p)
      (.call (some (continuation,link,l1,l2)) dest handler)
      {source with clock := source.clock + (bodyClock+continuationClock)} ≤
      bodyBudget + continuationBudget + 12 := by
  let entry : StackSemStateFiniteExact 64 LabToTarget.Config F :=
    {StackSemStateOps.setVar link (.loc l1 l2) (StackSemStateOps.decClock source) with
      clock := (StackSemStateOps.decClock source).clock + bodyClock}
  have actualEntry : StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2)
      {source with clock := source.clock + (bodyClock+continuationClock)}) =
      {entry with clock := entry.clock + continuationClock} := by
    simp only [entry, StackSemStateOps.decClock, StackSemStateOps.setVar]
    congr 1
    omega
  have liftedRun := Compiler.Backend.StackProps.evaluateAddClock continuationClock callee entry
    (result) post ⟨run, notTimeout⟩
  have stable := stackExecutionCost_addClock (price)
    callee entry post (result) run notTimeout continuationClock
  have bound := stackCost_returning_call_run (price := price) continuation link l1 l2 dest handler callee
    {source with clock := source.clock + (bodyClock+continuationClock)}
    {post with clock := post.clock + continuationClock} (result)
    (by simp only; omega) found (by rw [actualEntry]; exact liftedRun)
  rw [actualEntry, stable] at bound
  exact bound.trans (Nat.add_le_add_right (Nat.add_le_add bodyCost continuationCost) 12)

theorem stackCost_returning_call_composeHandler {F : Type}
    (callee continuation : HolProg 64) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (handler : Option (HolProg 64 × Nat × Nat))
    (source post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (bodyClock continuationClock bodyBudget continuationBudget : Nat)
    (nonzero : source.clock ≠ 0)
    (found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some callee)
    (run : StackSemEvaluate.evaluate
      (callee, {StackSemStateOps.setVar link (.loc l1 l2) (StackSemStateOps.decClock source) with
        clock := (StackSemStateOps.decClock source).clock + bodyClock}) =
      (some (.result (.loc l1 l2)), post))
    (bodyCost : stackExecutionCost (fun p _ => price p)
      callee {StackSemStateOps.setVar link (.loc l1 l2) (StackSemStateOps.decClock source) with
        clock := (StackSemStateOps.decClock source).clock + bodyClock} ≤ bodyBudget)
    (continuationCost : stackExecutionCost (fun p _ => price p)
      continuation {post with clock := post.clock + continuationClock} ≤ continuationBudget) :
    stackExecutionCost (fun p _ => price p)
      (.call (some (continuation,link,l1,l2)) dest handler)
      {source with clock := source.clock + (bodyClock+continuationClock)} ≤
      bodyBudget + continuationBudget + 12 := by
  apply stackCost_returning_call_composeSelected callee continuation link l1 l2 dest handler
    (some (.result (.loc l1 l2))) source post bodyClock continuationClock bodyBudget continuationBudget
    nonzero found run (by simp) bodyCost
  simpa only [selectedContinuationBudget, ↓reduceIte] using continuationCost

theorem stackCost_returning_call_compose {F : Type}
    (callee continuation : HolProg 64) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (source post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (bodyClock continuationClock bodyBudget continuationBudget : Nat)
    (nonzero : source.clock ≠ 0)
    (found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some callee)
    (run : StackSemEvaluate.evaluate
      (callee, {StackSemStateOps.setVar link (.loc l1 l2) (StackSemStateOps.decClock source) with
        clock := (StackSemStateOps.decClock source).clock + bodyClock}) =
      (some (.result (.loc l1 l2)), post))
    (bodyCost : stackExecutionCost (fun p _ => price p)
      callee {StackSemStateOps.setVar link (.loc l1 l2) (StackSemStateOps.decClock source) with
        clock := (StackSemStateOps.decClock source).clock + bodyClock} ≤ bodyBudget)
    (continuationCost : stackExecutionCost (fun p _ => price p)
      continuation {post with clock := post.clock + continuationClock} ≤ continuationBudget) :
    stackExecutionCost (fun p _ => price p)
      (.call (some (continuation,link,l1,l2)) dest none)
      {source with clock := source.clock + (bodyClock+continuationClock)} ≤
      bodyBudget + continuationBudget + 12 :=
  stackCost_returning_call_composeHandler callee continuation link l1 l2 dest none source post
    bodyClock continuationClock bodyBudget continuationBudget nonzero found run bodyCost continuationCost

#print axioms stackCost_returning_call_composeSelected
#print axioms stackCost_returning_call_composeHandler
#print axioms stackCost_returning_call_compose
end InitECandidate.Runtime.StackToLab
