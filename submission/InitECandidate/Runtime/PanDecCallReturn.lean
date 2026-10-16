import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A real declaration-call returns into its continuation with caller locals,
then restores the declaration's previous binding on leaving that continuation. -/
theorem evaluate_decCall_return_caller_locals {width : Nat} [NeZero width] {F : Type}
    (state post : PanSemStateFiniteExact width F) (name function : MlS)
    (shape returnShape : ShapeHOL) (arguments : List (ExpHOL width)) (values : List (ValueHOL width))
    (body continuation : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (value : ValueHOL width)
    (args : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (clock : state.clock ≠ 0)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (some (.returned value),post))
    (remaining : post.clock ≤ (callEntryStateHOLFinite state callee).clock)
    (declared : shapeEqHOL (shapeOfHOLExact value) shape = true)
    (returned : shapeEqHOL (shapeOfHOLExact value) returnShape = true) :
    evaluateHOLFiniteState state (.decCall name shape function arguments continuation) =
      (let output := evaluateHOLFiniteState
        (setVarHOLFinite name value {post with locals := state.locals}) continuation;
        (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
          (name,state.locals.lookup name))})) := by
  rw [evaluateHOLFiniteState_decCall_total,args]
  dsimp only
  rw [lookup]
  dsimp only
  rw [if_neg clock,run]
  dsimp only
  simp only [declared,returned,Bool.true_and,if_true,fixClockHOLFinite,
    if_neg (Nat.not_lt.mpr remaining)]

#print axioms evaluate_decCall_return_caller_locals
end InitECandidate.Runtime
