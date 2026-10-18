import InitECandidate.Runtime.StatelessReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Close a bounded prefix with a timeout-free continuation. Scope restoration
does not change the result or clock used by the runtime bound. -/
theorem evaluate_reaches_terminal_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (program tail : ProgHOL 64) (predicate : PanSemStateFiniteExact 64 F → Prop)
    (prefixCost tailCost : Nat) (budget : prefixCost + tailCost ≤ state.clock)
    (prefixRun : Reaches state program predicate prefixCost tail)
    (tailBound : ∀ next, predicate next → tailCost ≤ next.clock →
      let evaluated := evaluateHOLFiniteState next tail
      next.clock ≤ evaluated.2.clock + tailCost ∧ evaluated.2.clock ≤ next.clock ∧
        evaluated.1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state program
    state.clock ≤ evaluated.2.clock + (prefixCost + tailCost) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  rcases prefixRun with ⟨next,valid,spent,remaining,agreement⟩ | aborted
  · have bounded := tailBound next valid (by omega)
    obtain ⟨resultEq,clockEq,_,_,_⟩ := agreement
    dsimp only at bounded ⊢
    rw [resultEq,clockEq]
    exact ⟨by omega,by omega,bounded.2.2⟩
  · obtain ⟨result,run,_,spent,remaining,noTimeout⟩ := aborted
    refine ⟨by omega,remaining,?_⟩
    rw [run]
    exact fun equal => noTimeout (by omega) (Option.some.inj equal)

#print axioms evaluate_reaches_terminal_bounded
end InitECandidate.Runtime
