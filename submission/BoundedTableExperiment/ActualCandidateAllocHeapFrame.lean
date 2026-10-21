import ActualCandidateAllocEval

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A completed candidate scratch allocation (empty continuation) preserves
the heap memory exactly and advances `scratch_ptr` to the aligned allocation
end.  This is the PanSem heap-frame step of the candidate allocation
invariant. -/
theorem candidate_alloc_skip_heap {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (argument : ExpHOL 64) (size : BitVec 64)
    (pointer frame : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [argument] = some [.val (.word size)])
    (installed : state.code.lookup (ofString "scratch_alloc") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_scratch_alloc,.one))
    (clock : state.clock ≠ 0)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") =
      some (.val (.word pointer)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") =
      some (.val (.word frame)))
    (request : size ≤ pointer - frame)
    (finishBound : frame ≤ scratchAllocationEnd pointer size) :
    ∃ final, evaluateHOLFiniteState state
        (.decCall name .one (ofString "scratch_alloc") [argument] .skip) = (none, final) ∧
      final.memory = state.memory ∧
      final.globals = (setGlobalHOLFinite (ofString "scratch_ptr")
        (.val (.word (scratchAllocationEnd pointer size))) state).globals := by
  have h := candidate_alloc_eval_explicit state name argument
    size pointer frame arguments installed clock scratchGlobal frameGlobal request finishBound
  let final := { (setVarHOLFinite name
      (.val (.word (scratchAllocationEnd pointer size)))
      (candidateAllocReady state argument)) with
    locals := (setVarHOLFinite name
      (.val (.word (scratchAllocationEnd pointer size)))
      (candidateAllocReady state argument)).locals.resVarEq
        (name, state.locals.lookup name) }
  refine ⟨final, ?_, ?_, ?_⟩
  · rw [h.2.2]
    simp [final, evaluateHOLFiniteState_skip]
  · simp [final]
    exact h.1
  · simp [final]
    exact h.2.1

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidate_alloc_skip_heap
