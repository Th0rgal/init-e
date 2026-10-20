import InitECandidate.Runtime.StackExecutionCompleteJump
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Returning calls enter an installed callee after consuming a clock tick.
The saved return location is a caller-label fact, not a global register invariant. -/
theorem executionComplete_call_body {F : Type}
    {source middle : StackSemStateFiniteExact 64 LabToTarget.Config F}
    {rp prog : HolProg 64} {link l1 l2 dest handler result}
    (ih : ExecutionCompleteIH (.call (some (rp, link, l1, l2)) dest handler) source)
    (positive : source.clock ≠ 0)
    (found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog)
    (global : ExecutionCodeSupported source.code)
    (run : StackSemEvaluate.evaluate (prog,
      StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)) = (result, middle))
    (valid : ExecutionResultValid source.code result) :
    ExecutionTrace (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source))
      prog (executionKindOfResult result) middle := by
  obtain ⟨key, lookup⟩ := execution_findCode_lookup found
  have smaller : StackSemMeasure.LexNat
      ((StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)).clock, sizeOf prog)
      (source.clock, sizeOf (.call (some (rp, link, l1, l2)) dest handler : HolProg 64)) := by
    apply Prod.Lex.left
    change source.clock - 1 < source.clock
    omega
  exact ih prog _ smaller result middle run valid (global key prog lookup) global
    (ExecutionLabelScope.of_lookup lookup)

/-- A reached return/handler continuation inherits code and scope from the
callee trace, and its clock is strictly below the caller entry clock. -/
theorem executionComplete_call_continuation {F : Type}
    {source middle post : StackSemStateFiniteExact 64 LabToTarget.Config F}
    {rp prog continuation : HolProg 64} {link l1 l2 dest handler bodyResult result}
    (ih : ExecutionCompleteIH (.call (some (rp, link, l1, l2)) dest handler) source)
    (positive : source.clock ≠ 0)
    (bodyTree : ExecutionTrace (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source))
      prog (executionKindOfResult bodyResult) middle)
    (global : ExecutionCodeSupported source.code)
    (scope : ExecutionLabelScope source.code continuation)
    (supported : executionSupported continuation = true)
    (valid : ExecutionResultValid source.code result)
    (run : StackSemEvaluate.evaluate (continuation, middle) = (result, post)) :
    ExecutionTrace middle continuation (executionKindOfResult result) post := by
  have bodyRun := bodyTree.sound
  simp only [executionKindOfResult_result] at bodyRun
  have clockLe := StackSemEvaluateClock.evaluateClock prog _ bodyResult middle bodyRun
  have smaller : StackSemMeasure.LexNat (middle.clock, sizeOf continuation)
      (source.clock, sizeOf (.call (some (rp, link, l1, l2)) dest handler : HolProg 64)) := by
    apply Prod.Lex.left
    change middle.clock ≤ source.clock - 1 at clockLe
    omega
  have codeEq : middle.code = source.code := bodyTree.code_eq
  apply ih continuation middle smaller result post run
  · rw [codeEq]; exact valid
  · exact supported
  · rw [codeEq]; exact global
  · rw [codeEq]; exact scope

#print axioms executionComplete_call_body
#print axioms executionComplete_call_continuation
end InitECandidate.Runtime.StackToLab
