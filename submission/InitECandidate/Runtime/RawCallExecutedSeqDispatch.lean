import InitECandidate.Runtime.RawCallExecutedEarly
import InitECandidate.Runtime.RawCallFrameEligibility
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompSeqShape

namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall
open InitECandidate.Runtime.StackToLab

/-- Complete actual sequence dispatch: the top-level compiler preserves its
entry prologue; the recursive compiler may select one of three raw-tail
optimizations. Static source/code certificates discharge every frame price
condition, rather than assuming a bound on the resulting target run. -/
theorem executed_seq {F : Type} (bounds : BitVec 64 × BitVec 64)
    (first second : HolProg 64) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : Option (StackSemResult 64))
    (eligible : rawCallFramesSupported (.seq first second) = true)
    (codeEligible : RawCallFramesSupportedCode source.code)
    (firstIH : ExecutedProgramIH (refinedRemovalLocalPrice 6 bounds) first source)
    (secondIH : ∀ middle, StackSemEvaluate.evaluate (first, source) = (none, middle) →
      ExecutedProgramIH (refinedRemovalLocalPrice 6 bounds) second middle)
    (hypothesis : StackSemEvaluate.evaluate (.seq first second, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    ExecutedSimulationResult (refinedRemovalLocalPrice 6 bounds)
      (compTop info (.seq first second)) info target post result
      (stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 bounds p) (.seq first second) source) ∧
    ExecutedSimulationResult (refinedRemovalLocalPrice 6 bounds)
      (comp info (.seq first second)) info target post result
      (stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 bounds p) (.seq first second) source) := by
  have standard := executed_standard_seq (refinedRemovalLocalPrice 6 bounds)
    (fun a b => rfl) first second info source target post result firstIH secondIH hypothesis
  constructor
  · simpa only [compTop] using standard
  · change ExecutedSimulationResult (refinedRemovalLocalPrice 6 bounds)
      (compSeq first second info (.seq (comp info first) (comp info second)))
      info target post result _
    by_cases fallback : compSeq first second info (.seq (comp info first) (comp info second)) =
        .seq (comp info first) (comp info second)
    · rw [fallback]
      exact standard
    · obtain ⟨released, dest, rfl, rfl⟩ := compSeqNeqImp first second
        (.seq (comp info first) (comp info second)) info fallback
      have releaseFacts : 0 < released ∧ released ≤ 255 := by
        simpa [rawCallFramesSupported] using eligible
      cases frame : sptLookup dest info with
      | none => simp [compSeq, destCase, frame] at fallback
      | some allocated =>
        have frames : stateOk info source.code := by
          obtain ⟨_, _, _, frames, _⟩ := hypothesis.2.2
          exact frames
        obtain ⟨body, entry⟩ := frames dest allocated frame
        have entryEligible := codeEligible _ _ entry
        have allocationBound : allocated ≤ 255 := by
          simp only [rawCallFramesSupported, Bool.and_eq_true, decide_eq_true_eq] at entryEligible
          exact entryEligible.1
        simpa only [compSeq, destCase, frame] using
          executed_optimized_seq bounds released allocated dest info source target post result
            frame releaseFacts.1 releaseFacts.2 allocationBound secondIH hypothesis

#print axioms executed_seq
end InitECandidate.Runtime.StackRawCall
