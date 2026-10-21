import InitECandidate.Runtime.SourceCostGlobalsRunAssign
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
variable {fn : Flapjack.Pancake.PanLang.MlS}

theorem globals_declareValue (B : Nat) {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {name shape} {initializer : ExpHOL 64} {body : ProgHOL 64} {value : ValueHOL 64}
    {initEvents bodyEvents : List WorkEvent} {result}
    (init : CostedExpressionRun s initializer (some value) initEvents)
    (shapeMatch : shapeEqHOL shape (shapeOfHOLExact value) = true)
    (bodyRun : StatementRun fn (setVarHOLFinite name value s) body result post bodyEvents)
    (ih : GlobalsLe fn B (setVarHOLFinite name value s) body result post bodyEvents) :
    GlobalsLe fn B s (.dec name shape initializer body) result
      { post with locals := HolFiniteMapExact.resVarEq post.locals (name, s.locals.lookup name) }
      (.statement :: (initEvents ++ [.frame 1] ++ bodyEvents)) := by
  intro context t rel ok ready code h cov r' t' ev' target
  simp only [globalsReadyProg, Bool.and_eq_true, bne_iff_ne] at ready
  obtain ⟨hr, -⟩ := globals_sub_match (StatementRun.declareValue init shapeMatch bodyRun) ok rel target
  simp only [compileProgExactHOL] at target
  cases target
  case declareValue =>
    obtain ⟨hv, a⟩ := globals_costed B rel init (by assumption) ready.1.2
    cases hv
    have b := ih context _ (globalsRel_setVar rel name value) ok ready.2 code
      (globals_noTemp_setVar ready.1.1 _ h) cov _ _ _
      (by assumption : StatementRun fn _ (compileProgExactHOL context body) _ _ _)
    gsimp
    omega
  all_goals (cases hr; try exact absurd rfl ok)

#print axioms globals_declareValue
end InitECandidate.Runtime.FineCost
