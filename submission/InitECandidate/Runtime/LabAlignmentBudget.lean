import Flapjack.Compiler.Backend.LabProps.DomainAlignmentDmEvaluate
import Flapjack.Compiler.Backend.LabProps.DomainAlignmentSdmEvaluate
namespace InitECandidate.Runtime.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps

/-- Alignment changes domain representation without increasing label fuel or
changing terminal observations. Recover the unaligned run from the actual aligned run. -/
theorem unalign_terminating_same_clock {width : Nat} [NeZero width] {C F : Type}
    (dimension : goodDimindex width) (source post : State width C F) (outcome : HolOutcome)
    (run : evaluate (alignDm (alignSdm source)) = (.halt outcome, post)) :
    ∃ final, evaluate source = (.halt outcome, final) ∧ final.ffi = post.ffi := by
  have aligned := evaluateAlignDM dimension (alignSdm source)
  rw [evaluateAlignSDM dimension source] at aligned
  cases actual : evaluate source with
  | mk result final =>
    simp only [actual] at aligned
    rw [run] at aligned
    have parts := Prod.mk.inj aligned
    refine ⟨final, ?_, ?_⟩
    · rw [parts.1]
    · have ffi := congrArg (fun st => st.ffi) parts.2
      exact ffi.symm

#print axioms unalign_terminating_same_clock
end InitECandidate.Runtime.LabToTarget
