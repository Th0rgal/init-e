import InitECandidate.Runtime.StatelessReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A returned execution cannot have taken the abort alternative of a
bounded prefix. Its actual continuation retains the scoped result and state. -/
theorem reaches_returned_continuation {F : Type} (state : PanSemStateFiniteExact 64 F)
    (program tail : ProgHOL 64) (predicate : PanSemStateFiniteExact 64 F → Prop)
    (cost : Nat) (value : ValueHOL 64)
    (reached : Reaches state program predicate cost tail)
    (returned : (evaluateHOLFiniteState state program).1 = some (.returned value)) :
    ∃ next, predicate next ∧ state.clock ≤ next.clock + cost ∧ next.clock ≤ state.clock ∧
      Scoped (evaluateHOLFiniteState state program) (evaluateHOLFiniteState next tail) ∧
      (evaluateHOLFiniteState next tail).1 = some (.returned value) := by
  rcases reached with ⟨next,valid,spent,remaining,agreement⟩ | aborted
  · exact ⟨next,valid,spent,remaining,agreement,agreement.1.symm.trans returned⟩
  · obtain ⟨result,run,noReturn,_,_,_⟩ := aborted
    exact False.elim (noReturn value (Option.some.inj (run.symm.trans returned)))

/-- Transfer an exact global-state contract back across the prefix's scope
restoration, without assuming that any early rejection path succeeds. -/
theorem reaches_returned_globals {F : Type} (state : PanSemStateFiniteExact 64 F)
    (program tail : ProgHOL 64) (predicate : PanSemStateFiniteExact 64 F → Prop)
    (cost : Nat) (value : ValueHOL 64) (globals : HolFiniteMapExact MlS (ValueHOL 64))
    (reached : Reaches state program predicate cost tail)
    (returned : (evaluateHOLFiniteState state program).1 = some (.returned value))
    (tailGlobals : ∀ next, predicate next →
      (evaluateHOLFiniteState next tail).1 = some (.returned value) →
      (evaluateHOLFiniteState next tail).2.globals = globals) :
    (evaluateHOLFiniteState state program).2.globals = globals := by
  obtain ⟨next,valid,_,_,agreement,normal⟩ :=
    reaches_returned_continuation state program tail predicate cost value reached returned
  exact agreement.2.2.2.1.trans (tailGlobals next valid normal)

#print axioms reaches_returned_continuation
#print axioms reaches_returned_globals
end InitECandidate.Runtime
