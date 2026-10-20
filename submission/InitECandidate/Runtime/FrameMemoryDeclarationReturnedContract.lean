import InitECandidate.Runtime.FrameMemoryAllocationReturned
import InitECandidate.Runtime.VmFn_frame_mem_alloc
import InitECandidate.Runtime.PanSingleWordLookup
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- The original upward-workspace declaration resumes its actual continuation
at the old base, with exact frontier-only globals and real returned geometry. -/
theorem frame_memory_declaration_returned_contract {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (argument : ExpHOL 64) (tail : ProgHOL 64) (pointer size scratch : BitVec 64) (value : ValueHOL 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [argument]=some [.val (.word size)])
 (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word pointer)))
 (scratchGlobal : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (ordered : pointer.toNat≤scratch.toNat) (cap : scratch.toNat≤33806089496) (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.decCall name .one (ofString "frame_mem_alloc") [argument] tail)=(some (.returned value),post)) :
 ∃allocationPost output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (setVarHOLFinite name (.val (.word pointer)) {allocationPost with locals:=s.locals}) tail=
  (some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧
 allocationPost.memory=s.memory ∧allocationPost.memaddrs=s.memaddrs ∧allocationPost.be=s.be ∧allocationPost.code=s.code ∧
 allocationPost.globals=s.globals.update (ofString "frame_mem_ptr",.val (.word (allocationEnd pointer size))) ∧
 pointer.toNat+size.toNat≤(allocationEnd pointer size).toNat ∧
 (allocationEnd pointer size).toNat≤scratch.toNat ∧(allocationEnd pointer size).toNat%8=0 := by
 have installed : s.code.lookup (ofString "frame_mem_alloc")=
  some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_frame_mem_alloc,.one) := by
  rw [code];exact vmLookup_frame_mem_alloc
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=HolFiniteMapExact.empty.update (ofString "n",.val (.word size))
 have lookup:=pan_single_word_lookup s.code.lookup (ofString "frame_mem_alloc") (ofString "n")
  (sourceFunctionBody Guest.guestFn_frame_mem_alloc) size installed
 obtain ⟨allocated,allocationPost,output,allocationRun,checked,tailRun,postEq⟩:=
  evaluate_decCall_checked_returned_exact_scope s post name (ofString "frame_mem_alloc") .one .one _ _ _ _ callee value args lookup run
 let entry:=callEntryStateHOLFinite s callee
 have atSize : entry.locals.lookup (ofString "n")=some (.val (.word size)) := by
  simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 obtain ⟨returned,globals,coverage,within,aligned,memory,domain,endian,installedKept,clock⟩:=
  frame_memory_allocation_returned entry allocationPost pointer size scratch allocated frameGlobal scratchGlobal atSize ordered cap code allocationRun
 subst allocated
 exact ⟨allocationPost,output,tailRun,postEq,memory,domain,endian,installedKept,globals,coverage,within,aligned⟩
#print axioms frame_memory_declaration_returned_contract
end InitECandidate.Runtime
