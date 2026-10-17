import InitECandidate.Runtime.NamedGlobalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Checked callee binding frames and continuations preserve a named global through
actual declaration-call semantics, including timeouts and shape errors. -/
theorem evaluate_decCall_named_global_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (watched name function : MlS) (shape returnShape : ShapeHOL)
    (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (bodyFrame : (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.globals.lookup watched = state.globals.lookup watched)
    (tailRead : avoidsGlobalAssignment watched continuation = true) :
    let evaluated := evaluateHOLFiniteState state (.decCall name shape function arguments continuation);
    evaluated.2.globals.lookup watched = state.globals.lookup watched := by
  rw [evaluateHOLFiniteState_decCall_total,args]
  dsimp only
  rw [lookup]
  dsimp only
  split
  · rfl
  · rw [fixClockHOLFinite_evaluateState]
    have globals := bodyFrame
    cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
    | mk result bodyPost =>
      rw [bodyRun] at globals
      change bodyPost.globals.lookup watched = state.globals.lookup watched at globals
      cases result with
      | none => exact globals
      | some result =>
        cases result with
        | returned value =>
          simp only
          split
          · let resumed := setVarHOLFinite name value {bodyPost with locals := state.locals}
            have nextGlobals := evaluate_avoidsGlobalAssignment watched continuation tailRead resumed
            change (evaluateHOLFiniteState resumed continuation).2.globals.lookup watched = state.globals.lookup watched
            exact nextGlobals.trans globals
          · exact globals
        | error => exact globals
        | timeOut => exact globals
        | «break» => exact globals
        | «continue» => exact globals
        | exception exception value => exact globals
        | finalFfi ffi => exact globals

#print axioms evaluate_decCall_named_global_frame
end InitECandidate.Runtime
