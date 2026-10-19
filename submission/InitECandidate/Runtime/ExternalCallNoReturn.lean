import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem evaluate_external_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (function : MlS) (a b c d : ExpHOL 64) (value : ValueHOL 64) :
    (evaluateHOLFiniteState state (.extCall function a b c d)).1 ≠ some (.returned value) := by
  rw [evaluateHOLFiniteState_extCall_source]
  repeat' first | split | simp

#print axioms evaluate_external_no_return
end InitECandidate.Runtime
