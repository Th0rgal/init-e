import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- An actual tail call retains the callee's remaining clock, forwards or
rejects its result, and never falls through to the caller's next statement. -/
theorem evaluate_tailCall_body_bounded {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (function : MlS)
    (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (result : Option (PanSemResultExact 64)) (cost : Nat)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (nonzero : state.clock ≠ 0)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (result,post))
    (bound : state.clock ≤ post.clock + cost) (remaining : post.clock ≤ state.clock)
    (safe : result ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state (.call none function arguments)
    state.clock ≤ evaluated.2.clock + cost ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  rw [evaluateHOLFiniteState_call,args]
  dsimp only
  rw [lookup]
  dsimp only
  rw [if_neg nonzero,run]
  cases result with
  | none => exact ⟨bound,remaining,by simp,by simp⟩
  | some result =>
    cases result <;> simp_all [emptyLocalsHOLFinite]
    all_goals first | (exact ⟨bound,remaining⟩) | (split <;> simp_all)

#print axioms evaluate_tailCall_body_bounded
end InitECandidate.Runtime
