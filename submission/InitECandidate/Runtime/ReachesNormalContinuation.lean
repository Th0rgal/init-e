import InitECandidate.Runtime.StatelessReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Normal completion must pass through the actual bounded continuation;
the abort alternative always has a nonempty result. -/
theorem reaches_normal_continuation {F : Type} (state : PanSemStateFiniteExact 64 F)
    (program tail : ProgHOL 64) (predicate : PanSemStateFiniteExact 64 F → Prop)
    (cost : Nat) (reached : Reaches state program predicate cost tail)
    (normal : (evaluateHOLFiniteState state program).1 = none) :
    ∃ next, predicate next ∧ state.clock ≤ next.clock + cost ∧ next.clock ≤ state.clock ∧
      Scoped (evaluateHOLFiniteState state program) (evaluateHOLFiniteState next tail) ∧
      (evaluateHOLFiniteState next tail).1 = none := by
  rcases reached with ⟨next,valid,spent,remaining,agreement⟩ | aborted
  · exact ⟨next,valid,spent,remaining,agreement,agreement.1.symm.trans normal⟩
  · obtain ⟨result,run,_,_,_,_⟩ := aborted
    simp [normal] at run

/-- Extracting a continuation exposes its remaining budget for subsequent contracts. -/
theorem reaches_normal_continuation_budget {F : Type} (state : PanSemStateFiniteExact 64 F)
    (program tail : ProgHOL 64) (predicate : PanSemStateFiniteExact 64 F → Prop)
    (cost remaining : Nat) (reached : Reaches state program predicate cost tail)
    (budget : cost + remaining ≤ state.clock)
    (normal : (evaluateHOLFiniteState state program).1 = none) :
    ∃ next, predicate next ∧ remaining ≤ next.clock ∧
      Scoped (evaluateHOLFiniteState state program) (evaluateHOLFiniteState next tail) ∧
      (evaluateHOLFiniteState next tail).1 = none := by
  obtain ⟨next,valid,spent,_,agreement,tailNormal⟩ :=
    reaches_normal_continuation state program tail predicate cost reached normal
  exact ⟨next,valid,by omega,agreement,tailNormal⟩

#print axioms reaches_normal_continuation
#print axioms reaches_normal_continuation_budget
end InitECandidate.Runtime
