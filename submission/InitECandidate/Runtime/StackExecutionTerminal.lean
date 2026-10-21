import InitECandidate.Runtime.StackExecutionEligibility
namespace InitECandidate.Runtime.StackToLab
open Flapjack

/-- Terminal classification itself excludes error, timeout and invalid
location-valued halts, so a terminal caller needs no result-validity oracle. -/
theorem executionKindOfResult_terminal_valid {code : Spt (Compiler.Backend.StackLang.HolProg 64)}
    {result : StackSemResult 64} {outcome : HolOutcome}
    (terminal : executionKindOfResult (some result) = .terminal result outcome) :
    ExecutionResultValid code (some result) := by
  cases result <;> try (cases terminal)
  case halt value =>
    cases value with
    | loc _ _ => cases terminal
    | word _ => trivial
  case finalFFI event => trivial

#print axioms executionKindOfResult_terminal_valid
end InitECandidate.Runtime.StackToLab
