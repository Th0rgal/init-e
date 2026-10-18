import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Compose an assignment-form call and its actual subsequent program.
Only checked successful returns enter the continuation with the destination set. -/
theorem evaluate_localCall_continuation_bounded {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (name function : MlS)
    (returnShape : ShapeHOL) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (result : Option (PanSemResultExact 64)) (cost tailCost : Nat)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (nonzero : state.clock ≠ 0)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (result,post))
    (remaining : post.clock ≤ state.clock) (bound : state.clock ≤ post.clock + cost)
    (safe : result ≠ some .timeOut)
    (tail : ∀ value, result = some (.returned value) → shapeEqHOL (shapeOfHOLExact value) returnShape = true →
      let resumed := setVarHOLFinite name value {post with locals := state.locals}
      let evaluated := evaluateHOLFiniteState resumed continuation
      resumed.clock ≤ evaluated.2.clock + tailCost ∧ evaluated.2.clock ≤ resumed.clock ∧ evaluated.1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state
      (.seq (.call (some (some (.local,name),none)) function arguments) continuation)
    state.clock ≤ evaluated.2.clock + (cost + tailCost) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_call,args]
  dsimp only
  rw [lookup]
  dsimp only
  rw [if_neg nonzero,run]
  cases result with
  | none => exact ⟨by (try dsimp only [emptyLocalsHOLFinite]); omega,remaining,by simp⟩
  | some result =>
    cases result with
    | returned value =>
      by_cases checked : shapeEqHOL (shapeOfHOLExact value) returnShape = true
      · simp only [checked,if_true]
        by_cases assignable : isValidValueHOLExact state.toExact .local name value = true
        · simp only [assignable,if_true]
          let resumed := setVarHOLFinite name value {post with locals := state.locals}
          have next := tail value rfl checked
          change post.clock ≤ (evaluateHOLFiniteState resumed continuation).2.clock + tailCost ∧
            (evaluateHOLFiniteState resumed continuation).2.clock ≤ post.clock ∧
            (evaluateHOLFiniteState resumed continuation).1 ≠ some .timeOut at next
          change state.clock ≤ (evaluateHOLFiniteState resumed continuation).2.clock + (cost + tailCost) ∧
            (evaluateHOLFiniteState resumed continuation).2.clock ≤ state.clock ∧
            (evaluateHOLFiniteState resumed continuation).1 ≠ some .timeOut
          exact ⟨by omega,by omega,next.2.2⟩
        · simp [assignable] <;> omega
      · simp [checked] <;> omega
    | timeOut => exact False.elim (safe rfl)
    | error => exact ⟨by (try dsimp only [emptyLocalsHOLFinite]); omega,remaining,by simp⟩
    | «break» => exact ⟨by (try dsimp only [emptyLocalsHOLFinite]); omega,remaining,by simp⟩
    | «continue» => exact ⟨by (try dsimp only [emptyLocalsHOLFinite]); omega,remaining,by simp⟩
    | exception exception value => exact ⟨by (try dsimp only [emptyLocalsHOLFinite]); omega,remaining,by simp⟩
    | finalFfi ffi => exact ⟨by (try dsimp only [emptyLocalsHOLFinite]); omega,remaining,by simp⟩

#print axioms evaluate_localCall_continuation_bounded
end InitECandidate.Runtime
