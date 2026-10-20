import InitECandidate.Runtime.StatelessReach
import InitECandidate.Runtime.RunBounded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A reached continuation bound closes the full scoped prefix bound. -/
theorem runBounded_of_reaches {F : Type} (state : PanSemStateFiniteExact 64 F)
    (program continuation : ProgHOL 64) (predicate : PanSemStateFiniteExact 64 F→Prop)
    (prefixCost tailCost : Nat) (reached : Reaches state program predicate prefixCost continuation)
    (budget : prefixCost+tailCost≤state.clock)
    (tailBound : ∀ ready, predicate ready→tailCost≤ready.clock→RunBounded ready continuation tailCost) :
    RunBounded state program (prefixCost+tailCost) := by
  rcases reached with ⟨ready,valid,spent,remaining,agreement⟩|aborted
  · have tail := tailBound ready valid (by omega)
    unfold RunBounded at tail ⊢
    rw [agreement.1,agreement.2.1]
    exact ⟨by have := tail.1; omega,by have := tail.2.1; omega,tail.2.2⟩
  · obtain ⟨result,terminal,noReturn,spent,remaining,noTimeout⟩ := aborted
    refine ⟨by omega,remaining,?_⟩
    rw [terminal]
    intro timeout
    exact noTimeout (by omega) (Option.some.inj timeout)

#print axioms runBounded_of_reaches
end InitECandidate.Runtime
