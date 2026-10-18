import InitECandidate.Runtime.InitializerCounterSource
import InitECandidate.Runtime.InitializerCounterReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- EVM address initialization takes at most twenty loop ticks, or rejects
early on a failed byte store, before continuing its actual source suffix. -/
theorem evaluate_evmInit_counter_prefix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (budget : 20 ≤ state.clock) :
    Reaches state (evmInitAt 39) (InitializerCounterFinished state 20) 20 (evmInitAt 41) := by
  rw [source_evmInit_counter_declaration,source_evmInit_counter_loop]
  exact evaluate_initializer_counter_reaches state 20 evmInitCounterDestination (.const 255) (evmInitAt 41) (by decide) budget

/-- The seventeen precompile-address stores have the same bounded prefix
contract, including the declared counter and actual source continuation. -/
theorem evaluate_forkInit_counter_prefix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (budget : 17 ≤ state.clock) :
    Reaches state (forkInitAt 4) (InitializerCounterFinished state 17) 17 (forkInitAt 6) := by
  rw [source_forkInit_counter_declaration,source_forkInit_counter_loop]
  exact evaluate_initializer_counter_reaches state 17 forkInitCounterDestination forkInitCounterValue (forkInitAt 6) (by decide) budget

#print axioms evaluate_evmInit_counter_prefix
#print axioms evaluate_forkInit_counter_prefix
end InitECandidate.Runtime
