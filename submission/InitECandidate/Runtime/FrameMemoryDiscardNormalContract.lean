import InitECandidate.Runtime.FrameMemoryAllocationReturned
import InitECandidate.Runtime.VmFn_frame_mem_alloc
import InitECandidate.Runtime.PanSingleWordLookup
import InitECandidate.Runtime.PanDiscardNormalBody
import InitECandidate.Runtime.PanDiscardNormalBodyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Actual successful discard frame_mem_alloc call. Both original space guards
are extracted from its same returned body, with no room or fuel premise. -/
theorem frame_memory_discard_normal_contract {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (arguments : List (ExpHOL 64)) (pointer size scratch : BitVec 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some [.val (.word size)])
 (atPointer : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word pointer)))
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (ordered : pointer.toNat≤scratch.toNat) (cap : scratch.toNat≤33806089496)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "frame_mem_alloc") arguments)=(none,post)) :
 post.globals=s.globals.update (ofString "frame_mem_ptr",.val (.word (allocationEnd pointer size))) ∧
 pointer.toNat+size.toNat≤(allocationEnd pointer size).toNat ∧
 (allocationEnd pointer size).toNat≤scratch.toNat ∧(allocationEnd pointer size).toNat%8=0 ∧
 post.memory=s.memory ∧post.locals=s.locals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 have installed : s.code.lookup (ofString "frame_mem_alloc")=some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_frame_mem_alloc,.one) := by
  rw [code];exact vmLookup_frame_mem_alloc
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=HolFiniteMapExact.empty.update (ofString "n",.val (.word size))
 have lookup:=pan_single_word_lookup s.code.lookup (ofString "frame_mem_alloc") (ofString "n") (sourceFunctionBody Guest.guestFn_frame_mem_alloc) size installed
 obtain ⟨value,bodyPost,bodyRun,memory,locals⟩:=evaluate_discard_normal_body_memory s post (ofString "frame_mem_alloc") arguments _ _ callee .one args lookup run
 obtain ⟨other,otherPost,otherRun,globals,_⟩:=evaluate_discard_normal_body s post (ofString "frame_mem_alloc") arguments _ _ callee .one args lookup run
 have same : otherPost=bodyPost:=(Prod.mk.inj (bodyRun.symm.trans otherRun)).2.symm
 subst otherPost
 have atSize : (callEntryStateHOLFinite s callee).locals.lookup (ofString "n")=some (.val (.word size)) := by
  simp [callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 obtain ⟨_,globalKept,coverage,within,aligned,bodyMemory,_,_,_,_⟩:=frame_memory_allocation_returned (callEntryStateHOLFinite s callee) bodyPost pointer size scratch value atPointer atScratch atSize ordered cap code bodyRun
 have metadata:=evaluateHOLFiniteState_metadata s (.call (some (none,none)) (ofString "frame_mem_alloc") arguments)
 rw [run] at metadata
 exact ⟨globals.trans globalKept,coverage,within,aligned,memory.trans bodyMemory,locals,metadata.2.1,metadata.2.2.1,metadata.1⟩
#print axioms frame_memory_discard_normal_contract
end InitECandidate.Runtime
