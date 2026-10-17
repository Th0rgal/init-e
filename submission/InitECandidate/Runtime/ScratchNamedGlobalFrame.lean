import InitECandidate.Runtime.NamedGlobalFrame
import InitECandidate.Runtime.ScratchAllocationSuccess
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Scratch release may update its frontier but cannot alter another global. -/
theorem evaluate_scratchRelease_named_global {F : Type} (state : PanSemStateFiniteExact 64 F)
    (watched : MlS) (different : ofString "scratch_ptr" ≠ watched) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_scratch_release)).2.globals.lookup watched =
      state.globals.lookup watched := by
  apply evaluate_avoidsGlobalAssignment watched _ _ state
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  change (!(ofString "scratch_ptr" == watched) && true) = true
  simp [different]

/-- The original scratch mark is read-only at every clock and local shape. -/
theorem evaluate_scratchMark_named_global {F : Type} (state : PanSemStateFiniteExact 64 F) (watched : MlS) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_scratch_mark)).2.globals.lookup watched =
      state.globals.lookup watched := by
  apply evaluate_avoidsGlobalAssignment watched _ _ state
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Exact successful scratch allocation retains every other global binding,
including the heap frontier needed by later slice allocation. -/
theorem evaluate_scratchAlloc_success_named_global {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer size frame : BitVec 64) (watched : MlS) (different : ofString "scratch_ptr" ≠ watched)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (request : size ≤ pointer - frame) (finishBound : frame ≤ scratchAllocationEnd pointer size) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_scratch_alloc)).2.globals.lookup watched =
      state.globals.lookup watched := by
  obtain ⟨post,run,_,_,_,_,_,_,_,globals⟩ := evaluate_source_scratch_alloc_success state pointer size frame
    scratchGlobal sizeLocal frameGlobal request finishBound
  rw [run]
  dsimp only
  rw [globals]
  simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different]

#print axioms evaluate_scratchRelease_named_global
#print axioms evaluate_scratchMark_named_global
#print axioms evaluate_scratchAlloc_success_named_global
end InitECandidate.Runtime
