import InitECandidate.Runtime.WordSelectedPathCost
import InitECandidate.Runtime.WordPathWorkCorrect
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.WordInst Flapjack.Compiler.Encoders.Asm
open InitECandidate.Runtime.WordToStack

/-- Retains the complete pinned compiler simulation premises and postconditions.
This bounds additional Stack clock, not the final RISC-V instruction count. -/
theorem assignment_selected_stack_cost {C F : Type}
    (config : AsmConfigExact 64) (target temp : Nat)
    (expression : WordLangExpHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × C) F) :
    BoundedSimulation config (instSelect config temp (.assign target expression)) source
      (4 * wordExpressionWork expression) := by
  exact (wordPathWork_correct config _ source).mono
    (assignment_selected_path_bound config target temp expression source)

#print axioms assignment_selected_stack_cost
end InitECandidate.Runtime.FineCost
