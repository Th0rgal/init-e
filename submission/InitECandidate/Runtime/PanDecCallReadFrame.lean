import InitECandidate.Runtime.ReadOnlyGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Read-only callee bodies and continuations preserve memory/globals through
actual declaration-call semantics, including timeouts and shape errors. -/
theorem evaluate_decCall_readOnly_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name function : MlS) (shape returnShape : ShapeHOL)
    (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (bodyRead : readOnlyMemory body = true) (tailRead : readOnlyMemory continuation = true) :
    let evaluated := evaluateHOLFiniteState state (.decCall name shape function arguments continuation);
    evaluated.2.memory = state.memory ∧ evaluated.2.globals = state.globals := by
  rw [evaluateHOLFiniteState_decCall_total,args]
  dsimp only
  rw [lookup]
  dsimp only
  split
  · exact ⟨rfl,rfl⟩
  · rw [fixClockHOLFinite_evaluateState]
    have memory := evaluate_readOnly_memory body bodyRead (callEntryStateHOLFinite state callee)
    have globals := evaluate_readOnly_globals body bodyRead (callEntryStateHOLFinite state callee)
    cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
    | mk result bodyPost =>
      rw [bodyRun] at memory globals
      change bodyPost.memory = state.memory at memory
      change bodyPost.globals = state.globals at globals
      cases result with
      | none => exact ⟨memory,globals⟩
      | some result =>
        cases result with
        | returned value =>
          simp only
          split
          · let resumed := setVarHOLFinite name value {bodyPost with locals := state.locals}
            have nextMemory := evaluate_readOnly_memory continuation tailRead resumed
            have nextGlobals := evaluate_readOnly_globals continuation tailRead resumed
            change (evaluateHOLFiniteState resumed continuation).2.memory = state.memory ∧
              (evaluateHOLFiniteState resumed continuation).2.globals = state.globals
            exact ⟨nextMemory.trans memory,nextGlobals.trans globals⟩
          · exact ⟨memory,globals⟩
        | error => exact ⟨memory,globals⟩
        | timeOut => exact ⟨memory,globals⟩
        | «break» => exact ⟨memory,globals⟩
        | «continue» => exact ⟨memory,globals⟩
        | exception exception value => exact ⟨memory,globals⟩
        | finalFfi ffi => exact ⟨memory,globals⟩

#print axioms evaluate_decCall_readOnly_frame
end InitECandidate.Runtime
