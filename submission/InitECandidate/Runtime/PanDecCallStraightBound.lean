import InitECandidate.Runtime.StraightLineNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A checked call-body clock bound extends through a straight-line
continuation. Body and return-shape failures are covered as terminal outcomes. -/
theorem evaluate_decCall_straight_bounded {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (name function : MlS)
    (shape returnShape : ShapeHOL) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (result : Option (PanSemResultExact 64)) (cost : Nat)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (nonzero : state.clock ≠ 0)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (result,post))
    (remaining : post.clock ≤ (callEntryStateHOLFinite state callee).clock)
    (bound : state.clock ≤ post.clock + cost)
    (noTimeout : result ≠ some .timeOut)
    (supported : straightLine continuation = true) :
    let evaluated := evaluateHOLFiniteState state (.decCall name shape function arguments continuation);
    state.clock ≤ evaluated.2.clock + cost ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
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
  | none => exact ⟨bound,postRemaining,by simp⟩
  | some result =>
    cases result with
    | returned value =>
      simp only
      split
      · let resumed := setVarHOLFinite name value {post with locals := state.locals}
        have clock := clockPreserving_of_straightLine continuation supported resumed
        have terminal := evaluate_straightLine_no_timeout continuation supported resumed
        change state.clock ≤ (evaluateHOLFiniteState resumed continuation).2.clock + cost ∧
          (evaluateHOLFiniteState resumed continuation).2.clock ≤ state.clock ∧
          (evaluateHOLFiniteState resumed continuation).1 ≠ some .timeOut
        change (evaluateHOLFiniteState resumed continuation).2.clock = post.clock at clock
        exact ⟨by omega,by omega,terminal⟩
      · exact ⟨bound,postRemaining,by simp⟩
    | timeOut => exact False.elim (noTimeout rfl)
    | error => exact ⟨bound,postRemaining,by simp⟩
    | «break» => exact ⟨bound,postRemaining,by simp⟩
    | «continue» => exact ⟨bound,postRemaining,by simp⟩
    | exception exception value => exact ⟨bound,postRemaining,by simp⟩
    | finalFfi ffi => exact ⟨bound,postRemaining,by simp⟩

#print axioms evaluate_decCall_straight_bounded
end InitECandidate.Runtime
