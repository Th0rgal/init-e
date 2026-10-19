import InitECandidate.Runtime.ReadOnlyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A read-only callee can be followed by a writing continuation whose footprint
is independently bounded. This covers all evaluator outcomes and clock sizes. -/
theorem evaluate_decCall_watched_memory {F : Type}
    (state : PanSemStateFiniteExact 64 F) (name function : MlS)
    (shape returnShape : ShapeHOL) (arguments : List (ExpHOL 64))
    (values : List (ValueHOL 64)) (body continuation : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (watched : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (bodyRead : readOnlyMemory body = true)
    (tailFrame : ∀ (value : ValueHOL 64) (ready : PanSemStateFiniteExact 64 F),
      shapeEqHOL (shapeOfHOLExact value) shape = true →
      ready.locals = state.locals → ready.memory = state.memory →
      (evaluateHOLFiniteState (setVarHOLFinite name value ready) continuation).2.memory watched = ready.memory watched) :
    (evaluateHOLFiniteState state (.decCall name shape function arguments continuation)).2.memory watched = state.memory watched := by
  rw [evaluateHOLFiniteState_decCall_total,args]
  dsimp only
  rw [lookup]
  dsimp only
  split
  · rfl
  · rw [fixClockHOLFinite_evaluateState]
    have memory := evaluate_readOnly_memory body bodyRead (callEntryStateHOLFinite state callee)
    cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
    | mk result bodyPost =>
      rw [bodyRun] at memory
      change bodyPost.memory = state.memory at memory
      cases result with
      | none => exact congrFun memory watched
      | some result =>
        cases result with
        | returned value =>
          simp only
          split
          · rename_i goodShape
            let ready : PanSemStateFiniteExact 64 F := {bodyPost with locals := state.locals}
            change (evaluateHOLFiniteState (setVarHOLFinite name value ready) continuation).2.memory watched = state.memory watched
            have shapes : shapeEqHOL (shapeOfHOLExact value) shape = true ∧
                shapeEqHOL (shapeOfHOLExact value) returnShape = true := by
              simpa only [Bool.and_eq_true] using goodShape
            exact (tailFrame value ready shapes.1 rfl memory).trans (congrFun memory watched)
          · exact congrFun memory watched
        | error => exact congrFun memory watched
        | timeOut => exact congrFun memory watched
        | «break» => exact congrFun memory watched
        | «continue» => exact congrFun memory watched
        | exception exception value => exact congrFun memory watched
        | finalFfi ffi => exact congrFun memory watched

#print axioms evaluate_decCall_watched_memory
end InitECandidate.Runtime
