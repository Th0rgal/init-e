import InitECandidate.Runtime.TrapNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Shared-memory writes either continue, fail, or end at the host. They
preserve the source clock and every local binding in all three cases. -/
theorem evaluate_shared_store_control_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (operator : OpSize) (address value : ExpHOL 64) :
    let evaluated := evaluateHOLFiniteState state (.shMemStore operator address value)
    (evaluated.1 = none ∨ evaluated.1 = some .error ∨ ∃ event, evaluated.1 = some (.finalFfi event)) ∧
      evaluated.2.clock = state.clock ∧
      ∀ key, evaluated.2.locals.lookup key = state.locals.lookup key := by
  classical
  rw [evaluateHOLFiniteState_shMemStore_total]
  dsimp only
  split
  · unfold shMemStoreHOLExact
    split <;> split
    all_goals simp [ofExact,toExact]
    all_goals split <;> simp
  · simp

#print axioms evaluate_shared_store_control_frame
end InitECandidate.Runtime
