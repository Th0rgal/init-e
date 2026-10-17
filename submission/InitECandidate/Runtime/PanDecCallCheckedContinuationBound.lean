import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Compose a checked callee clock bound with a checked continuation bound.
Body and return-shape failures are covered as terminal outcomes. -/
theorem evaluate_decCall_checked_continuation_bounded {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (name function : MlS)
    (shape returnShape : ShapeHOL) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (result : Option (PanSemResultExact 64)) (cost tailCost : Nat)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (nonzero : state.clock ≠ 0)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (result,post))
    (remaining : post.clock ≤ (callEntryStateHOLFinite state callee).clock)
    (bound : state.clock ≤ post.clock + cost)
    (noTimeout : result ≠ some .timeOut)
    (continuationBound : ∀ value, result = some (.returned value) →
      (shapeEqHOL (shapeOfHOLExact value) shape && shapeEqHOL (shapeOfHOLExact value) returnShape) = true →
      let resumed := setVarHOLFinite name value {post with locals := state.locals}
      let evaluated := evaluateHOLFiniteState resumed continuation
      resumed.clock ≤ evaluated.2.clock + tailCost ∧ evaluated.2.clock ≤ resumed.clock ∧ evaluated.1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state (.decCall name shape function arguments continuation);
    state.clock ≤ evaluated.2.clock + (cost + tailCost) ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have postRemaining : post.clock ≤ state.clock := by
    change post.clock ≤ state.clock - 1 at remaining
    omega
  rw [evaluateHOLFiniteState_decCall_total,args]
  dsimp only
  rw [lookup]
  dsimp only
  rw [if_neg nonzero,run]
  have fixed : fixClockHOLFinite (callEntryStateHOLFinite state callee) (result,post) = (result,post) := by
    simp [fixClockHOLFinite,Nat.not_lt.mpr remaining]
  rw [fixed]
  dsimp only
  cases result with
  | none => exact ⟨by change state.clock ≤ post.clock + (cost + tailCost); omega,postRemaining,by simp⟩
  | some result =>
    cases result with
    | returned value =>
      simp only
      split
      · rename_i checkedShape
        let resumed := setVarHOLFinite name value {post with locals := state.locals}
        have tail := continuationBound value rfl checkedShape
        change post.clock ≤ (evaluateHOLFiniteState resumed continuation).2.clock + tailCost ∧
          (evaluateHOLFiniteState resumed continuation).2.clock ≤ post.clock ∧
          (evaluateHOLFiniteState resumed continuation).1 ≠ some .timeOut at tail
        change state.clock ≤ (evaluateHOLFiniteState resumed continuation).2.clock + (cost + tailCost) ∧
          (evaluateHOLFiniteState resumed continuation).2.clock ≤ state.clock ∧
          (evaluateHOLFiniteState resumed continuation).1 ≠ some .timeOut
        exact ⟨by omega,by omega,tail.2.2⟩
      · exact ⟨by change state.clock ≤ post.clock + (cost + tailCost); omega,postRemaining,by simp⟩
    | timeOut => exact False.elim (noTimeout rfl)
    | error => exact ⟨by change state.clock ≤ post.clock + (cost + tailCost); omega,postRemaining,by simp⟩
    | «break» => exact ⟨by change state.clock ≤ post.clock + (cost + tailCost); omega,postRemaining,by simp⟩
    | «continue» => exact ⟨by change state.clock ≤ post.clock + (cost + tailCost); omega,postRemaining,by simp⟩
    | exception exception value => exact ⟨by change state.clock ≤ post.clock + (cost + tailCost); omega,postRemaining,by simp⟩
    | finalFfi ffi => exact ⟨by change state.clock ≤ post.clock + (cost + tailCost); omega,postRemaining,by simp⟩

#print axioms evaluate_decCall_checked_continuation_bounded
end InitECandidate.Runtime
