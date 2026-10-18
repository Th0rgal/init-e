import InitECandidate.Runtime.AuthorizationsTailSource
import InitECandidate.Runtime.NormalLocalIncrement
import InitECandidate.Runtime.StraightLineNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem authorizationLastStore_increments : NormalLocalIncrement (ofString "i") authorizationLastStore := by
  rw [source_authorization_last_store]
  apply normalLocalIncrement_seq _ _ _ (by rfl)
  exact normalLocalIncrement_assign _

/-- Normal completion of the actual record-tail store advances the outer
loop index exactly once, without any extra source clock consumption. -/
theorem evaluate_authorization_last_store_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (index : BitVec 64) (binding : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (run : evaluateHOLFiniteState state authorizationLastStore = (none,post)) :
    post.locals.lookup (ofString "i") = some (.val (.word (index + 1))) ∧ post.clock = state.clock := by
  have clock := clockPreserving_of_straightLine authorizationLastStore authorizationLastStore_straight state
  rw [run] at clock
  exact ⟨authorizationLastStore_increments state post index binding run,clock⟩

#print axioms evaluate_authorization_last_store_progress
end InitECandidate.Runtime
