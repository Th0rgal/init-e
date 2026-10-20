import InitECandidate.Runtime.FrameMemoryAllocationReturned
import InitECandidate.Runtime.InterpreterFundingLayout
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful real upward workspace allocation preserves every live
funding record; no fresh-allocation footprint or successful-space callback is
assumed, since this allocator writes only its global frontier. -/
theorem interpreter_funding_frame_memory_allocation {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (lower upper : Nat) (frames : List InterpreterFundingFrame)
 (valid : InterpreterFundingLayout s lower upper frames)
 (pointer size scratch : BitVec 64) (value : ValueHOL 64)
 (atPointer : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word pointer)))
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (atSize : s.locals.lookup (ofString "n")=some (.val (.word size)))
 (ordered : pointer.toNat≤scratch.toNat) (cap : scratch.toNat≤33806089496)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_frame_mem_alloc)=(some (.returned value),post)) :
 InterpreterFundingLayout post lower upper frames ∧
 value=.val (.word pointer) ∧pointer.toNat+size.toNat≤(allocationEnd pointer size).toNat ∧
 (allocationEnd pointer size).toNat≤scratch.toNat ∧(allocationEnd pointer size).toNat%8=0 := by
 obtain ⟨returned,globals,coverage,within,aligned,memory,domain,endian,codeKept,clock⟩:=
  frame_memory_allocation_returned s post pointer size scratch value atPointer atScratch atSize ordered cap code run
 refine ⟨?_,returned,coverage,within,aligned⟩
 refine ⟨valid.upperBound,?_,valid.disjoint,valid.budget⟩
 intro frame member
 exact (valid.records frame member).after_frame (post:=post) domain (by intro offset present;rw [memory])
#print axioms interpreter_funding_frame_memory_allocation
end InitECandidate.Runtime
