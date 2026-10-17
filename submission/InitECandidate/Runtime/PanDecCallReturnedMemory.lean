import InitECandidate.Runtime.PanDecCallReturnedBodyScope
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Returned declaration-calls preserve memory when their successful callee
and continuation do; code equality is available to the continuation proof. -/
theorem evaluate_decCall_returned_memory {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (name function : MlS)
    (shape returnShape : ShapeHOL) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (finalValue : ValueHOL 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (bodyRead : ∀ value output, evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
      (some (.returned value),output) → output.memory = state.memory)
    (tailRead : ∀ (ready output : PanSemStateFiniteExact 64 F) value,
      ready.code = state.code → evaluateHOLFiniteState (setVarHOLFinite name value ready) continuation =
        (some (.returned finalValue),output) → output.memory = ready.memory)
    (run : evaluateHOLFiniteState state (.decCall name shape function arguments continuation) =
      (some (.returned finalValue),post)) : post.memory = state.memory := by
  obtain ⟨value,bodyPost,ready,output,bodyRun,_,memory,_,_,code,tail,restored⟩ :=
    evaluate_decCall_returned_body_scope state post name function shape returnShape arguments values
      body continuation callee finalValue args lookup run
  have bodyMemory := bodyRead value bodyPost bodyRun
  have metadata := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body
  rw [bodyRun] at metadata
  have readyCode : ready.code = state.code := code.trans metadata.1
  rw [restored]
  exact (tailRead ready output value readyCode tail).trans (memory.trans bodyMemory)

#print axioms evaluate_decCall_returned_memory
end InitECandidate.Runtime
