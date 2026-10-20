import InitECandidate.Runtime.StackExecutionCostAddClock
import InitECandidate.Runtime.StackNativeGapPrice
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Seq
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Original stack-removal postcondition, including terminal FFI agreement. -/
def RemovalCostPost {F : Type} (jump : Bool) (bounds : BitVec 64 × BitVec 64) (pointer : Nat)
    (post targetPost : StackSemStateFiniteExact 64 LabToTarget.Config F) : Option (StackSemResult 64) → Prop
  | some (.halt _) | some .timeOut | some (.finalFFI _) => targetPost.ffi = post.ffi
  | _ => StackRemove.stateRelHOL jump bounds pointer post targetPost

/-- Original semantic simulation with an additional executed-cost conclusion.
No target run, native trace or whole-run budget is supplied as a premise. -/
def RemovalCostSimulation {F : Type} (sourcePrice : HolProg 64 → Nat) (gap : Nat) (jump : Bool) (bounds : BitVec 64 × BitVec 64)
    (program : HolProg 64) (source : StackSemStateFiniteExact 64 LabToTarget.Config F) : Prop :=
  ∀ (post target : StackSemStateFiniteExact 64 LabToTarget.Config F) result pointer,
    StackSemEvaluate.evaluate (program, source) = (result, post) ∧ result ≠ some .error ∧
      StackRemove.stateRelHOL jump bounds pointer source target ∧ StackProps.regBound program pointer →
    ∃ clock postTarget,
      StackSemEvaluate.evaluate (StackRemove.comp jump bounds pointer program,
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      RemovalCostPost jump bounds pointer post postTarget result ∧
      stackExecutionCost (fun p _ => nativePriceWithGap gap p) (StackRemove.comp jump bounds pointer program)
        {target with clock := clock + target.clock} ≤ stackExecutionCost (fun p _ => sourcePrice p) program source

/-- Sequential composition keeps only the reached suffix and sums the two
compiler clock witnesses without increasing either executed cost. -/
theorem removalCostSimulation_seq {F : Type} (sourcePrice : HolProg 64 → Nat) (gap : Nat) (jump : Bool) (bounds : BitVec 64 × BitVec 64)
    (first second : HolProg 64) (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (firstIH : RemovalCostSimulation sourcePrice gap jump bounds first source)
    (secondIH : ∀ middle, StackSemEvaluate.evaluate (first, source) = (none, middle) →
      RemovalCostSimulation sourcePrice gap jump bounds second middle) :
    RemovalCostSimulation sourcePrice gap jump bounds (.seq first second) source := by
  intro post target result pointer premises
  obtain ⟨run, nonerror, related, lower⟩ := premises
  change StackProps.regBound first pointer ∧ StackProps.regBound second pointer at lower
  rw [StackRemove.CompCorrect.Seq.evaluateSeqUnclamped] at run
  rcases firstRun : StackSemEvaluate.evaluate (first, source) with ⟨firstResult, middle⟩
  rw [firstRun] at run
  cases firstResult with
  | none =>
    obtain ⟨firstClock, middleTarget, firstTargetRun, middleRelation, firstCost⟩ :=
      firstIH middle target none pointer ⟨firstRun, by simp, related, lower.1⟩
    obtain ⟨secondClock, postTarget, secondTargetRun, postRelation, secondCost⟩ :=
      secondIH middle firstRun post middleTarget result pointer ⟨run, nonerror, middleRelation, lower.2⟩
    have shiftedRun := StackProps.evaluateAddClock secondClock
      (StackRemove.comp jump bounds pointer first) {target with clock := firstClock + target.clock}
      none middleTarget ⟨firstTargetRun, by simp⟩
    have combinedRun : StackSemEvaluate.evaluate (StackRemove.comp jump bounds pointer first,
        {target with clock := (firstClock + secondClock) + target.clock}) =
        (none, {middleTarget with clock := secondClock + middleTarget.clock}) := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using shiftedRun
    have shiftedCost := stackExecutionCost_addClock (nativePriceWithGap gap)
      (StackRemove.comp jump bounds pointer first) {target with clock := firstClock + target.clock}
      middleTarget none firstTargetRun (by simp) secondClock
    have combinedCost : stackExecutionCost (fun p _ => nativePriceWithGap gap p)
        (StackRemove.comp jump bounds pointer first) {target with clock := (firstClock + secondClock) + target.clock} ≤
        stackExecutionCost (fun p _ => sourcePrice p) first source := by
      have eq : stackExecutionCost (fun p _ => nativePriceWithGap gap p)
          (StackRemove.comp jump bounds pointer first) {target with clock := (firstClock + secondClock) + target.clock} =
          stackExecutionCost (fun p _ => nativePriceWithGap gap p)
            (StackRemove.comp jump bounds pointer first) {target with clock := firstClock + target.clock} := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using shiftedCost
      exact eq.le.trans firstCost
    refine ⟨firstClock + secondClock, postTarget, ?_, postRelation, ?_⟩
    · rw [StackRemove.comp, StackRemove.CompCorrect.Seq.evaluateSeqNone _ _ _ _ combinedRun]
      exact secondTargetRun
    · rw [StackRemove.comp, stackExecutionCost_seq, combinedRun, stackExecutionCost_seq, firstRun]
      simp only [show nativePriceWithGap gap (.seq (StackRemove.comp jump bounds pointer first) (StackRemove.comp jump bounds pointer second)) = 0 from rfl, Nat.zero_add]
      omega
  | some value =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    obtain ⟨clock, postTarget, targetRun, postRelation, cost⟩ :=
      firstIH middle target (some value) pointer ⟨firstRun, nonerror, related, lower.1⟩
    refine ⟨clock, postTarget, ?_, postRelation, ?_⟩
    · rw [StackRemove.comp, StackRemove.CompCorrect.Seq.evaluateSeqSome _ _ _ _ _ targetRun]
    · rw [StackRemove.comp, stackExecutionCost_seq, targetRun, stackExecutionCost_seq, firstRun]
      simp only [show nativePriceWithGap gap (.seq (StackRemove.comp jump bounds pointer first) (StackRemove.comp jump bounds pointer second)) = 0 from rfl, Nat.zero_add, Nat.add_zero]
      omega

#print axioms removalCostSimulation_seq
end InitECandidate.Runtime.StackToLab
