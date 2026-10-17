import Flapjack.Pancake.Semantics.PanProps.EvalInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The concrete finite evaluator preserves the original accessible addresses. -/
theorem evaluateHOLFiniteState_memaddrs {F : Type} (state : PanSemStateFiniteExact 64 F) (program : ProgHOL 64) :
    (evaluateHOLFiniteState state program).2.memaddrs = state.memaddrs := by
  have invariant := evaluateInvariantsHOLFinite program
    (PanPropsEvalStateFiniteExact.ofPanSemFinite state)
    (evaluateHOLFiniteState state program).1
    (PanPropsEvalStateFiniteExact.ofPanSemFinite (evaluateHOLFiniteState state program).2) (by
      simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
        PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite]
      )
  exact invariant.1

#print axioms evaluateHOLFiniteState_memaddrs
end InitECandidate.Runtime
