import InitECandidate.Runtime.FrameNewSource
import InitECandidate.Runtime.MarkerDeclarationReturnedContext
import InitECandidate.Runtime.ScratchMarkCall
import InitECandidate.Runtime.VmFn_frame_mem_mark
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def frameNewMarksEntry {F : Type} (s : PanSemStateFiniteExact 64 F) (scratch frame : BitVec 64) : PanSemStateFiniteExact 64 F :=
 let first:=setVarHOLFinite (ofString "stack_mark") (.val (.word scratch)) {s with clock:=s.clock-1}
 setVarHOLFinite (ofString "mem_mark") (.val (.word frame)) {first with clock:=first.clock-1}

/-- Both original marker callees are executed and inverted; no assumed
callee execution or minimum-fuel premise is used. -/
theorem frame_new_marks_returned_context {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (scratch frame : BitVec 64) (value : ValueHOL 64)
 (scratchGlobal : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)))
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (frameNewAt 0)=(some (.returned value),post)) :
 ∃output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (frameNewMarksEntry s scratch frame) (frameNewAt 2)=(some (.returned value),output) ∧
 post.memory=output.memory ∧post.globals=output.globals ∧post.memaddrs=output.memaddrs ∧post.be=output.be ∧post.code=output.code := by
 rw [source_frame_new_0] at run
 have scratchInstalled : s.code.lookup (ofString "scratch_mark")=some ([],sourceFunctionBody Guest.guestFn_scratch_mark,.one) := by
  rw [code];exact originalRuntimeCode_scratchMark_lookup
 obtain ⟨middle,middleRun,postEq⟩:=marker_declaration_returned_context s post (ofString "stack_mark") (ofString "scratch_mark")
  (ofString "scratch_ptr") (sourceFunctionBody Guest.guestFn_scratch_mark) (frameNewAt 1) scratch value scratchInstalled source_scratchMark_body scratchGlobal run
 let first:=setVarHOLFinite (ofString "stack_mark") (.val (.word scratch)) {s with clock:=s.clock-1}
 change evaluateHOLFiniteState first (frameNewAt 1)=_ at middleRun
 rw [source_frame_new_1] at middleRun
 have frameInstalled : first.code.lookup (ofString "frame_mem_mark")=some ([],sourceFunctionBody Guest.guestFn_frame_mem_mark,.one) := by
  change s.code.lookup _=_
  rw [code];exact vmLookup_frame_mem_mark
 have source : sourceFunctionBody Guest.guestFn_frame_mem_mark=.return (.var .global (ofString "frame_mem_ptr")) := by rw [sourceFunctionBody_eq_structural];rfl
 obtain ⟨output,bodyRun,middleEq⟩:=marker_declaration_returned_context first middle (ofString "mem_mark") (ofString "frame_mem_mark")
  (ofString "frame_mem_ptr") (sourceFunctionBody Guest.guestFn_frame_mem_mark) (frameNewAt 2) frame value frameInstalled source frameGlobal middleRun
 refine ⟨output,bodyRun,?_,?_,?_,?_,?_⟩
 all_goals rw [postEq,middleEq]

#print axioms frame_new_marks_returned_context
end InitECandidate.Runtime
