import InitECandidate.Runtime.RawCallExecutedSeqDispatch
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Call.Return

namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.CallCase
open Flapjack.Compiler.Backend.StackRawCall.RawCallCase
open InitECandidate.Runtime.StackToLab

abbrev ExecutedReturnCalleeIH {F : Type} (price : HolProg 64 → Nat)
    (dest : Sum Nat Nat) (link l1 l2 : Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) : Prop :=
  ∀ program, findCode dest (source.regs.eraseEq link) source.code = some program →
    source.clock ≠ 0 → ∀ info target post result,
      StackSemEvaluate.evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
        (result, post) ∧ result ≠ some .error ∧
        stateRel info (decClock (setVar link (.loc l1 l2) source)) target →
      ExecutedSimulationResult price (compTop info program) info target post result
        (stackExecutionCost (fun p _ => price p) program (decClock (setVar link (.loc l1 l2) source)))

abbrev ExecutedReturnContinuationIH {F : Type} (price : HolProg 64 → Nat)
    (ret : HolProg 64) (dest : Sum Nat Nat) (link l1 l2 : Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) : Prop :=
  ∀ program, findCode dest (source.regs.eraseEq link) source.code = some program →
    source.clock ≠ 0 → ∀ middle,
      StackSemEvaluate.evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
        (some (.result (.loc l1 l2)), middle) → ExecutedProgramIH price ret middle

abbrev ExecutedExceptionContinuationIH {F : Type} (price : HolProg 64 → Nat)
    (handler : Option (HolProg 64 × Nat × Nat)) (dest : Sum Nat Nat) (link l1 l2 : Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) : Prop :=
  ∀ program h hl1 hl2,
    findCode dest (source.regs.eraseEq link) source.code = some program → source.clock ≠ 0 →
    handler = some (h, hl1, hl2) → ∀ middle,
      StackSemEvaluate.evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
        (some (.exception (.loc hl1 hl2)), middle) → ExecutedProgramIH price h middle

/-- Construct the actual transformed callee run and its cost from the
quantitative source IH. Restore outer frame information only after proving it
survives that actual callee execution. -/
theorem executed_returning_callee {F : Type} (price : HolProg 64 → Nat)
    (dest : Sum Nat Nat) (link l1 l2 : Nat) (info : Spt Nat)
    (source target middle : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (program : HolProg 64) (result : Option (StackSemResult 64))
    (calleeIH : ExecutedReturnCalleeIH price dest link l1 l2 source)
    (relation : stateRel info source target)
    (lookup : findCode dest (source.regs.eraseEq link) source.code = some program)
    (nonzero : source.clock ≠ 0)
    (execution : StackSemEvaluate.evaluate
      (program, decClock (setVar link (.loc l1 l2) source)) = (result, middle))
    (nonerror : result ≠ some .error) :
    ∃ entryInfo, findCode dest (target.regs.eraseEq link) target.code =
        some (compTop entryInfo program) ∧
      ExecutedSimulationResult price (compTop entryInfo program) info
        (decClock (setVar link (.loc l1 l2) target)) middle result
        (stackExecutionCost (fun p _ => price p) program (decClock (setVar link (.loc l1 l2) source))) := by
  obtain ⟨entryInfo, entryRelation, targetLookup⟩ :=
    callEntryErased info source target relation dest link program lookup
  obtain ⟨clock, targetMiddle, space, middleRelation, targetExecution, guard, cost⟩ :=
    calleeIH program lookup nonzero entryInfo
      (decClock (setVar link (.loc l1 l2) target)) middle result
      ⟨execution, nonerror, LoopCase.stateRel_decClock entryInfo
        (setVar link (.loc l1 l2) source) (setVar link (.loc l1 l2) target)
        (stateRel_setVar entryInfo source target entryRelation link (.loc l1 l2))⟩
  have frames : stateOk info source.code := by
    obtain ⟨_, _, _, frames, _⟩ := relation
    exact frames
  have middleFrames := stateOk_afterEvaluate info program
    (decClock (setVar link (.loc l1 l2) source)) middle result frames execution
  exact ⟨entryInfo, targetLookup, clock, targetMiddle, space,
    stateRel_changeInfo entryInfo info middle targetMiddle middleRelation middleFrames,
    targetExecution, guard, cost⟩

#print axioms executed_returning_callee
end InitECandidate.Runtime.StackRawCall
