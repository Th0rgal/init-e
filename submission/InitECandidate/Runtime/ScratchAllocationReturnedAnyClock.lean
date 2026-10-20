import InitECandidate.Runtime.ScratchAllocationReturnedProgress
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- Remove the conservative one-tick caller requirement from the actual
returned scratch-allocation contract by replaying that same completed run
with one added clock tick. No successful-space premise is added. -/
theorem scratch_allocation_returned_progress_any_clock {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (pointer size frame : BitVec 64) (value : ValueHOL 64)
 (scratchGlobal : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word pointer)))
 (sizeLocal : s.locals.lookup (ofString "n")=some (.val (.word size)))
 (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)))
 (ordered : frame≤pointer) (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_scratch_alloc)=(some (.returned value),post)) :
 value=.val (.word (scratchAllocationEnd pointer size)) ∧
 post.globals.lookup (ofString "scratch_ptr")=some (.val (.word (scratchAllocationEnd pointer size))) ∧
 frame.toNat≤(scratchAllocationEnd pointer size).toNat ∧
 (scratchAllocationEnd pointer size).toNat+size.toNat≤pointer.toNat ∧
 post.memory=s.memory ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 have replay:=panPropsEvaluateAddClockEq (sourceFunctionBody Guest.guestFn_scratch_alloc) s _ post 1 ⟨run,by simp⟩
 exact scratch_allocation_returned_progress {s with clock:=s.clock+1} {post with clock:=post.clock+1}
  pointer size frame value scratchGlobal sizeLocal frameGlobal ordered code (by change 1≤s.clock+1;omega) replay

/-- The exact global endpoint of the same successful original allocator. -/
theorem scratch_allocation_returned_globals_any_clock {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (pointer size frame : BitVec 64) (value : ValueHOL 64)
 (scratchGlobal : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word pointer)))
 (sizeLocal : s.locals.lookup (ofString "n")=some (.val (.word size)))
 (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)))
 (ordered : frame≤pointer) (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_scratch_alloc)=(some (.returned value),post)) :
 post.globals=s.globals.update (ofString "scratch_ptr",.val (.word (scratchAllocationEnd pointer size))) := by
 obtain ⟨returned,global,lower,extent,memory,domain,endian,installed⟩:=
  scratch_allocation_returned_progress_any_clock s post pointer size frame value scratchGlobal sizeLocal frameGlobal ordered code run
 have request : size≤pointer-frame := by
  apply BitVec.le_def.mpr
  rw [BitVec.toNat_sub_of_le ordered]
  omega
 have within : frame≤scratchAllocationEnd pointer size:=BitVec.le_def.mpr lower
 obtain ⟨expected,success,_,_,_,_,_,_,_,globals⟩:=evaluate_source_scratch_alloc_success s pointer size frame scratchGlobal sizeLocal frameGlobal request within
 have equal : post=expected := by
  rw [returned] at run
  exact (Prod.mk.inj (run.symm.trans success)).2
 rw [equal,globals]
 rfl
#print axioms scratch_allocation_returned_globals_any_clock
#print axioms scratch_allocation_returned_progress_any_clock
end InitECandidate.Runtime
