import InitECandidate.Runtime.StackExecutionCompleteCall
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Every successful supported evaluator run has the finite semantic derivation
used by the native-step theorem. There is no derivation or native budget premise. -/
theorem executionTrace_of_evaluate {F : Type} (p : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    ExecutionCompleteAt p source := by
  have ih : ExecutionCompleteIH p source := by
    intro q child smaller
    exact executionTrace_of_evaluate q child
  by_cases atomic : executionAtomic p = true
  · intro result post run valid _ _ _
    exact executionTrace_atomic source post p result atomic run valid
  · cases p <;> try (simp [executionAtomic] at atomic)
    all_goals try (solve | intro result post run valid supported; simp [executionSupported] at supported)
    case seq first second => exact executionComplete_seq first second source ih
    case ite cmp reg operand yes no => exact executionComplete_ite yes no cmp reg operand source ih
    case loop body => exact executionComplete_loop body source ih
    case rawCall dest => exact executionComplete_raw dest source ih
    case jumpLower regX regY dest => exact executionComplete_jump regX regY dest source ih
    case call ret dest handler =>
      cases ret with
      | none =>
        cases handler with
        | none => exact executionComplete_tail dest source ih
        | some packet =>
          intro result post run valid supported
          simp [executionSupported] at supported
      | some packet =>
        rcases packet with ⟨rp, link, l1, l2⟩
        exact executionComplete_call rp link l1 l2 dest handler source ih
termination_by (source.clock, sizeOf p)
decreasing_by exact smaller

#print axioms executionTrace_of_evaluate
end InitECandidate.Runtime.StackToLab
