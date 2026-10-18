import InitECandidate.Runtime.PanDecCallCheckedContinuationBound
import InitECandidate.Runtime.StraightLineNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Compose inside the original declaration scope after a straight prefix. -/
theorem evaluate_decCall_append_bounded {F : Type}
    (state bodyPost : PanSemStateFiniteExact 64 F) (name function : MlS)
    (shape returnShape : ShapeHOL) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body first tail : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (result : Option (PanSemResultExact 64)) (cost tailCost : Nat)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (nonzero : state.clock ≠ 0)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (result,bodyPost))
    (remaining : bodyPost.clock ≤ (callEntryStateHOLFinite state callee).clock)
    (bound : state.clock ≤ bodyPost.clock + cost) (noTimeout : result ≠ some .timeOut)
    (straight : straightLine first = true)
    (tailBound : ∀ value, result = some (.returned value) →
      (shapeEqHOL (shapeOfHOLExact value) shape = true ∧ shapeEqHOL (shapeOfHOLExact value) returnShape = true) →
      ∀ output, evaluateHOLFiniteState (setVarHOLFinite name value {bodyPost with locals := state.locals}) first = (none,output) →
      let evaluated := evaluateHOLFiniteState output tail
      output.clock ≤ evaluated.2.clock + tailCost ∧ evaluated.2.clock ≤ output.clock ∧ evaluated.1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state (.decCall name shape function arguments (.seq first tail))
    state.clock ≤ evaluated.2.clock + (cost + tailCost) ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  apply evaluate_decCall_checked_continuation_bounded state bodyPost name function shape returnShape arguments values body (.seq first tail)
    callee result cost tailCost args lookup nonzero run remaining bound noTimeout
  intro value returned checked
  have checkedBoth : shapeEqHOL (shapeOfHOLExact value) shape = true ∧ shapeEqHOL (shapeOfHOLExact value) returnShape = true := by simpa using checked
  let resumed := setVarHOLFinite name value {bodyPost with locals := state.locals}
  have clock := clockPreserving_of_straightLine first straight resumed
  have safe := evaluate_straightLine_no_timeout first straight resumed
  change resumed.clock ≤ (evaluateHOLFiniteState resumed (.seq first tail)).2.clock + tailCost ∧
    (evaluateHOLFiniteState resumed (.seq first tail)).2.clock ≤ resumed.clock ∧
    (evaluateHOLFiniteState resumed (.seq first tail)).1 ≠ some .timeOut
  rw [evaluateHOLFiniteState_seq_line780]
  cases firstRun : evaluateHOLFiniteState resumed first with
  | mk firstResult output =>
    rw [firstRun] at clock safe
    dsimp only at clock safe ⊢
    cases firstResult with
    | some stopped =>
      dsimp only
      exact ⟨by omega,by omega,safe⟩
    | none =>
      dsimp only
      have bounded := tailBound value returned checkedBoth output firstRun
      exact ⟨by dsimp only at bounded; omega,by dsimp only at bounded; omega,bounded.2.2⟩

#print axioms evaluate_decCall_append_bounded
end InitECandidate.Runtime
