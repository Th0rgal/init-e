import InitECandidate.Runtime.StackCallRunCost
import InitECandidate.Runtime.WordStackReturnCopyCost
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Runtime.StackToLab

variable {price : HolProg 64 → Nat} [caps : ConservativeRemovalPrice price]

private theorem seqStackFree_cost_from_run {F : Type} (count : Nat) (body : HolProg 64)
    (source restored : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (small : count ≤ 92)
    (run : StackSemEvaluate.evaluate (seqStackFreeNative count .skip, source) = (none, restored)) :
    stackExecutionCost (fun p _ => price p)
      (seqStackFreeNative count body) source ≤ 7*count +
      stackExecutionCost (fun p _ => price p) body restored := by
  by_cases zero : count = 0
  · simp only [seqStackFreeNative, zero, ↓reduceIte, StackSemEvaluate.evaluate_skip, Prod.mk.injEq, true_and] at run
    subst restored
    simp only [seqStackFreeNative, zero, ↓reduceIte, Nat.mul_zero, Nat.zero_add, Nat.le_refl]
  · rw [seqStackFreeNative, if_neg zero, StackSemEvaluate.evaluate_seq,
      StackSemEvaluateClock.fixClockEvaluate] at run
    rcases headRun : StackSemEvaluate.evaluate (.stackFree count, source) with ⟨result, middle⟩
    rw [headRun] at run
    cases result with
    | some result => cases (Prod.mk.inj run).1
    | none =>
      simp only [StackSemEvaluate.evaluate_skip, Prod.mk.injEq, true_and] at run
      subst restored
      have bound := stackCost_seq_run (price := price) (.stackFree count) body source middle 7 headRun
        (by simpa only [stackExecutionCost] using ConservativeRemovalPrice.free count small)
      rw [seqStackFreeNative, if_neg zero]
      exact bound.trans (by omega)

/-- Return-slot copying composes with the continuation at the actual restored
state, rather than requiring a uniform continuation ceiling over all states. -/
theorem wordStack_copyRet_cost_run {F β γ : Type} (isHandle : Bool)
    (kf : Nat × Nat × γ) (values : List β) (body : HolProg 64)
    (source restored : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (frameSmall : kf.2.1 ≤ 92)
    (returnsSmall : Flapjack.Compiler.Backend.WordToStack.numStackRet kf.1 values ≤ 92)
    (run : StackSemEvaluate.evaluate (copyRetNative false isHandle kf values .skip, source) = (none, restored)) :
    stackExecutionCost (fun p _ => price p)
      (copyRetNative false isHandle kf values body) source ≤
      21 * Flapjack.Compiler.Backend.WordToStack.numStackRet kf.1 values +
      stackExecutionCost (fun p _ => price p) body restored := by
  let n := Flapjack.Compiler.Backend.WordToStack.numStackRet kf.1 values
  let offset := if isHandle then kf.2.1 + Flapjack.Compiler.Backend.WordToStack.handlerSlots false else kf.2.1
  have fits : n+offset ≤ 256 := by
    cases isHandle <;> simp only [offset, Bool.false_eq_true, ↓reduceIte, Flapjack.Compiler.Backend.WordToStack.handlerSlots] <;> omega
  change StackSemEvaluate.evaluate
    ((if n=0 then .skip else .seq (copyRetAuxNative kf.1 offset n) (seqStackFreeNative n .skip)), source) = (none, restored) at run
  change stackExecutionCost _ (if n=0 then body else .seq (copyRetAuxNative kf.1 offset n) (seqStackFreeNative n body)) source ≤ 21*n + _
  by_cases zero : n=0
  · simp only [zero, ↓reduceIte, StackSemEvaluate.evaluate_skip, Prod.mk.injEq, true_and] at run
    subst restored
    simp only [zero, ↓reduceIte, Nat.mul_zero, Nat.zero_add, Nat.le_refl]
  · rw [if_neg zero, StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate] at run
    rcases copiesRun : StackSemEvaluate.evaluate (copyRetAuxNative kf.1 offset n, source) with ⟨result, middle⟩
    rw [copiesRun] at run
    cases result with
    | some result => cases (Prod.mk.inj run).1
    | none =>
      have copies := (ConservativeRemovalPrice.execution (price := price)
        (copyRetAuxNative kf.1 offset n) source).trans (wordStack_copyRetAux_cost kf.1 offset n fits source)
      have prefixBound := stackCost_seq_run (price := price) (copyRetAuxNative kf.1 offset n)
        (seqStackFreeNative n body) source middle (14*n) copiesRun copies
      have suffixBound := seqStackFree_cost_from_run (price := price) n body middle restored returnsSmall run
      rw [if_neg zero]
      omega

#print axioms wordStack_copyRet_cost_run
end InitECandidate.Runtime.WordToStack
