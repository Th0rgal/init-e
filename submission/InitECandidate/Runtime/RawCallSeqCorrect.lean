import InitECandidate.Runtime.RawCallOptimizedBudget
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompSeqShape
namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall

/-- Full bounded Seq case, including all three tail-frame optimization forms. -/
theorem compCorrectSeq {width : Nat} [NeZero width] {C F : Type}
    (first second : HolProg width) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (firstIH : ProgramIH C F first source)
    (secondIH : SeqSecondIH C F first second source)
    (hypothesis : StackSemEvaluate.evaluate (.seq first second, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulationResult (compTop info (.seq first second)) info target post result (source.clock - post.clock) ∧
    BoundedSimulationResult (comp info (.seq first second)) info target post result (source.clock - post.clock) := by
  have standard := simulateStandardSeq first second info source target post result
    firstIH secondIH hypothesis
  constructor
  · simpa only [compTop] using standard
  · change BoundedSimulationResult (compSeq first second info (.seq (comp info first) (comp info second)))
      info target post result (source.clock - post.clock)
    by_cases fallback : compSeq first second info (.seq (comp info first) (comp info second)) =
        .seq (comp info first) (comp info second)
    · rw [fallback]
      exact standard
    · obtain ⟨released, dest, rfl, rfl⟩ := compSeqNeqImp first second
        (.seq (comp info first) (comp info second)) info fallback
      cases frame : sptLookup dest info with
      | none => simp [compSeq, destCase, frame] at fallback
      | some allocated =>
          simpa only [compSeq, destCase, frame] using
            simulateOptimizedSeq released allocated dest info source target post result
              frame secondIH hypothesis


#print axioms compCorrectSeq
end InitECandidate.Runtime.StackRawCall
