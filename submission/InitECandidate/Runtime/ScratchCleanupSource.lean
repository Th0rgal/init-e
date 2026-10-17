import InitECandidate.Runtime.ScratchAllocationSource
import InitECandidate.Runtime.StraightLineNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_scratch_mark : sourceFunctionBody Guest.guestFn_scratch_mark =
    .return (.var .global (ofString "scratch_ptr")) := by
  simp only [sourceFunctionBody,Guest.guestFn_scratch_mark,declToHOL,funDeclToHOL,progToHOL,expToHOL]

theorem source_scratch_release : sourceFunctionBody Guest.guestFn_scratch_release =
    .seq (.assign .global (ofString "scratch_ptr") (.var .local (ofString "m"))) (.return (.const 0)) := by
  simp only [sourceFunctionBody,Guest.guestFn_scratch_release,declToHOL,funDeclToHOL,progToHOL,expToHOL]
  rfl

/-- The original mark body returns the current scratch pointer without ticks. -/
theorem evaluate_scratch_mark_body {F : Type} (state : PanSemStateFiniteExact 64 F) (scratch : BitVec 64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch))) :
    evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_scratch_mark) =
      (some (.returned (.val (.word scratch))),emptyLocalsHOLFinite state) := by
  rw [source_scratch_mark]
  simp [evaluateHOLFiniteState_return,evalHOLExact,scratchGlobal,shapeOfHOLExact]

/-- The original release body restores the saved scratch pointer and returns
zero without changing memory or spending source clock. -/
theorem evaluate_scratch_release_body {F : Type} (state : PanSemStateFiniteExact 64 F) (scratch mark : BitVec 64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (markLocal : state.locals.lookup (ofString "m") = some (.val (.word mark))) :
    evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_scratch_release) =
      (some (.returned (.val (.word 0))),emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "scratch_ptr") (.val (.word mark)) state)) := by
  have assigned : evaluateHOLFiniteState state (.assign .global (ofString "scratch_ptr") (.var .local (ofString "m"))) =
      (none,setGlobalHOLFinite (ofString "scratch_ptr") (.val (.word mark)) state) := by
    simp [evaluateHOLFiniteState_assign,evalHOLExact,markLocal,lookupKvarHOLExact,scratchGlobal,
      isValidValueHOLExact,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite]
  rw [source_scratch_release,evaluateHOLFiniteState_seq_line780,assigned]
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]

#print axioms evaluate_scratch_mark_body
#print axioms evaluate_scratch_release_body
end InitECandidate.Runtime
