import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A word declaration adds no ticks to a uniform body bound. Invalid
initializers terminate immediately and are included in the contract. -/
theorem evaluate_dec_one_uniform_clock_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (initializer : ExpHOL 64) (body : ProgHOL 64) (cost : Nat)
    (bounded : ∀ word : BitVec 64,
      let evaluated := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word word)) state) body
      state.clock ≤ evaluated.2.clock + cost ∧ evaluated.2.clock ≤ state.clock ∧
        evaluated.1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state (.dec name .one initializer body)
    state.clock ≤ evaluated.2.clock + cost ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  rw [evaluateHOLFiniteState_dec_total]
  cases initial : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) initializer with
  | none => simp [initial]
  | some value =>
    simp only [initial]
    cases value with
    | rStruct fields => simp [shapeOfHOLExact,shapeEqHOL]
    | nStruct name fields => simp [shapeOfHOLExact,shapeEqHOL]
    | val atom =>
      cases atom with
      | word word =>
        simp only [shapeOfHOLExact,shapeEqHOL,if_true]
        cases run : evaluateHOLFiniteState (setVarHOLFinite name (.val (.word word)) state) body with
        | mk result post =>
          have bound := bounded word
          rw [run] at bound
          exact bound

#print axioms evaluate_dec_one_uniform_clock_bounded
end InitECandidate.Runtime
