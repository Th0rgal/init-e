import InitECandidate.Runtime.PanDecCallReturnedGlobalScope
import InitECandidate.Runtime.LookupCodeInstalledBody
import InitECandidate.Runtime.ReadOnlyGlobals
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned call to an installed read-only helper keeps the heap value
available to its actual continuation, with no argument-success premise. -/
theorem evaluate_readOnly_decCall_returned_heap {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (name function : MlS) (shape : ShapeHOL)
    (arguments : List (ExpHOL 64)) (continuation body : ProgHOL 64)
    (parameters : List (MlS × ShapeHOL)) (returnShape : ShapeHOL)
    (heap : BitVec 64) (finalValue : ValueHOL 64)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (readOnly : readOnlyMemory body = true) (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (tail : ∀ (next output : PanSemStateFiniteExact 64 F), next.code = originalRuntimeCode →
      next.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) →
      evaluateHOLFiniteState next continuation = (some (.returned finalValue),output) →
      output.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (.decCall name shape function arguments continuation) =
      (some (.returned finalValue),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => rw [evaluateHOLFiniteState_decCall_total,args] at run; cases run
  | some values =>
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => rw [evaluateHOLFiniteState_decCall_lookup_none state name shape function arguments continuation values args lookup] at run; cases run
    | some found =>
      obtain ⟨foundBody,callee,foundShape⟩ := found
      have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body foundBody
        returnShape foundShape values callee (by rw [code]; exact installed) lookup
      subst foundBody
      obtain ⟨value,bodyPost,ready,output,bodyRun,_,globals,_,_,readyCode,tailRun,postEq⟩ :=
        evaluate_decCall_returned_global_scope state post name function shape foundShape arguments values
          body continuation callee finalValue args lookup run
      have bodyGlobals := evaluate_readOnly_globals body readOnly (callEntryStateHOLFinite state callee)
      have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body
      rw [bodyRun] at bodyGlobals meta'
      have nextHeap : (setVarHOLFinite name value ready).globals.lookup (ofString "heap_ptr") =
          some (.val (.word heap)) := by
        change ready.globals.lookup _ = _
        rw [globals,bodyGlobals]
        exact atHeap
      have result := tail (setVarHOLFinite name value ready) output
        (readyCode.trans (meta'.1.trans code)) nextHeap tailRun
      rw [postEq]
      exact result

#print axioms evaluate_readOnly_decCall_returned_heap
end InitECandidate.Runtime
