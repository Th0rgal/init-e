import ActualCandidateAllocHeapFrame
import InitECandidate.Runtime.RlpEncodeBytesPrefix
import ActualCandidateScratchEval

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 1000000

/-- A completed scratch allocation leaves every other local unchanged.  This is
the chaining fact for the six frozen allocation frames: the caller's `cap`
survives each `decCall`. -/
theorem candidate_alloc_skip_locals {F : Type} (state : PanSemStateFiniteExact 64 F)
    (ready : PanSemStateFiniteExact 64 F)
    (name name' : MlS) (argument : ExpHOL 64) (size pointer : BitVec 64)
    (continuationEq : ∀ (callName : MlS) (continuation : ProgHOL 64),
      evaluateHOLFiniteState state
          (.decCall callName .one (ofString "scratch_alloc") [argument] continuation) =
        (let output := evaluateHOLFiniteState
            (setVarHOLFinite callName (.val (.word (scratchAllocationEnd pointer size))) ready)
            continuation;
          (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
            (callName,state.locals.lookup callName))})))
    (readyLocals : ready.locals = state.locals)
    (hne : name' ≠ name) :
    (evaluateHOLFiniteState state
      (.decCall name .one (ofString "scratch_alloc") [argument] .skip)).2.locals.lookup name' =
        state.locals.lookup name' := by
  rw [continuationEq name .skip]
  simp only [evaluateHOLFiniteState_skip]
  rw [lookup_resVarEq_ne _ name name' _ hne]
  rw [HolFiniteMapExact.lookup_update]
  simp [hne]

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidate_alloc_skip_locals
