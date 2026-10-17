import InitECandidate.Runtime.AllocationSource
import InitECandidate.Runtime.ConditionalTrapBound
import InitECandidate.Runtime.PanSeqStraightBound
import InitECandidate.Runtime.PanSequenceTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The allocator's original rounded-end guard, heap update and return
cost at most one tick at arbitrary locals/globals, including malformed values. -/
theorem evaluate_allocationFinish_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state allocationFinish
    state.clock ≤ evaluated.2.clock + 1 ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  obtain ⟨result,post,run,cost,remaining,noTimeout,_⟩ := evaluate_conditional_trap_bounded state
    (.cmp .lower (.const 33806089496) (.var .local (ofString "q"))) 1 code ticks
  have bound := evaluate_sequence_straight_bounded state
    (.ite (.cmp .lower (.const 33806089496) (.var .local (ofString "q")))
      (.call (some (none,none)) (ofString "trap_with") [.const 1]) .skip)
    (.seq (.assign .global (ofString "heap_ptr") (.var .local (ofString "q"))) (.return (.var .local (ofString "p"))))
    1 (by rw [run]; exact ⟨cost,remaining,noTimeout⟩) (by decide)
  have terminal : (evaluateHOLFiniteState state allocationFinish).1 ≠ none := by
    unfold allocationFinish
    apply evaluate_seq_terminal
    intro middle
    apply evaluate_seq_terminal
    intro final
    exact evaluate_return_terminal final _
  exact ⟨bound.1,bound.2.1,bound.2.2,terminal⟩

#print axioms evaluate_allocationFinish_bounded
end InitECandidate.Runtime
