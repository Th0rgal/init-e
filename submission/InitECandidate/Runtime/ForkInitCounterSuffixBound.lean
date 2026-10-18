import InitECandidate.Runtime.ForkInitSuffixBound
import InitECandidate.Runtime.InitializerCounterPrefixes
import InitECandidate.Runtime.ReachesTerminalBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The counter declaration, seventeen iterations and complete address suffix
of the original fork initializer need at most 119 source ticks. -/
theorem evaluate_forkInit_counter_suffix_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (budget : 119 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (forkInitAt 4)
    state.clock ≤ evaluated.2.clock + 119 ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  exact evaluate_reaches_terminal_bounded state (forkInitAt 4) (forkInitAt 6)
    (InitializerCounterFinished state 17) 17 102 budget
    (evaluate_forkInit_counter_prefix state (by omega))
    (by
      intro next valid fuel
      exact evaluate_forkInit_suffix_bounded next (valid.2.1.trans code) fuel)

#print axioms evaluate_forkInit_counter_suffix_bounded
end InitECandidate.Runtime
