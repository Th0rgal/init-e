import InitECandidate.Runtime.RawCallSeqBudget
import InitECandidate.Runtime.StackExecutionCostAddClock

namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall
open InitECandidate.Runtime.StackToLab

/-- Original raw-call simulation witness, with a bound on the actual compiled
execution counter at that same witness clock. Resource exceptions are retained. -/
def ExecutedSimulationResult {F : Type} (price : HolProg 64 → Nat)
    (compiled : HolProg 64) (info : Spt Nat)
    (target post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : Option (StackSemResult 64)) (budget : Nat) : Prop :=
  ∃ clock targetState stackSpace,
    stateRel info post targetState ∧
    StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + clock}) =
      (result, {targetState with stackSpace := stackSpace}) ∧
    ((result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat 64 2)))) →
      stackSpace = targetState.stackSpace) ∧
    stackExecutionCost (fun p _ => price p) compiled
      {target with clock := target.clock + clock} ≤ budget

/-- Quantitative recursive hypothesis: the target run and its bound must both
be constructed, for the actual recursively compiled syntax and code relation. -/
def ExecutedProgramIH {F : Type} (price : HolProg 64 → Nat) (p : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) : Prop :=
  ∀ info target post result,
    StackSemEvaluate.evaluate (p, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target →
    ExecutedSimulationResult price (comp info p) info target post result
      (stackExecutionCost (fun p _ => price p) p source)

/-- Standard sequence composition from genuine quantitative recursive IHs.
The first compiled run is extended by the second witness's clock; cost
stability proves this extension does not charge another execution. -/
theorem executed_standard_seq {F : Type} (price : HolProg 64 → Nat)
    (freeSeq : ∀ a b, price (.seq a b) = 0)
    (first second : HolProg 64) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : Option (StackSemResult 64))
    (firstIH : ExecutedProgramIH price first source)
    (secondIH : ∀ middle, StackSemEvaluate.evaluate (first, source) = (none, middle) →
      ExecutedProgramIH price second middle)
    (hypothesis : StackSemEvaluate.evaluate (.seq first second, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    ExecutedSimulationResult price (.seq (comp info first) (comp info second))
      info target post result
      (stackExecutionCost (fun p _ => price p) (.seq first second) source) := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  rcases firstRun : StackSemEvaluate.evaluate (first, source) with ⟨firstResult, middle⟩
  rw [SeqCase.evaluateSeqUnclamped, firstRun] at execution
  cases firstResult with
  | none =>
    obtain ⟨firstClock, targetMiddle, firstSpace, middleRelation, firstTargetRun, firstGuard, firstCost⟩ :=
      firstIH info target middle none ⟨firstRun, by simp, relation⟩
    have spaceEq := firstGuard (by simp)
    subst firstSpace
    have spaceSelf : {targetMiddle with stackSpace := targetMiddle.stackSpace} = targetMiddle := by
      cases targetMiddle; rfl
    rw [spaceSelf] at firstTargetRun
    obtain ⟨secondClock, targetPost, finalSpace, postRelation, secondTargetRun, finalGuard, secondCost⟩ :=
      secondIH middle firstRun info targetMiddle post result ⟨execution, nonerror, middleRelation⟩
    have extended := StackProps.evaluateAddClock secondClock (comp info first)
      {target with clock := target.clock + firstClock} none targetMiddle ⟨firstTargetRun, by simp⟩
    have stable := stackExecutionCost_addClock price (comp info first)
      {target with clock := target.clock + firstClock} targetMiddle none firstTargetRun (by simp) secondClock
    have inputEq : {{target with clock := target.clock + firstClock} with
        clock := target.clock + firstClock + secondClock} =
        {target with clock := target.clock + (firstClock + secondClock)} := by
      simp only [Nat.add_assoc]
    rw [inputEq] at extended stable
    refine ⟨firstClock + secondClock, targetPost, finalSpace, postRelation, ?_, finalGuard, ?_⟩
    · rw [SeqCase.evaluateSeqUnclamped, extended]
      exact secondTargetRun
    · rw [stackExecutionCost_seq, extended, stackExecutionCost_seq, firstRun]
      simp only [freeSeq, Nat.zero_add]
      rw [stable]
      exact Nat.add_le_add firstCost secondCost
  | some firstResult =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
    obtain ⟨clock, targetPost, finalSpace, postRelation, targetRun, guard, cost⟩ :=
      firstIH info target middle (some firstResult) ⟨firstRun, nonerror, relation⟩
    refine ⟨clock, targetPost, finalSpace, postRelation, ?_, guard, ?_⟩
    · rw [SeqCase.evaluateSeqUnclamped, targetRun]
    · rw [stackExecutionCost_seq, targetRun, stackExecutionCost_seq, firstRun]
      simpa only [freeSeq, Nat.zero_add, Nat.add_zero] using cost

#print axioms executed_standard_seq
end InitECandidate.Runtime.StackRawCall
