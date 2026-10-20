import InitECandidate.Runtime.ScratchAllocationReturnedAnyClock
import InitECandidate.Runtime.ScratchAllocationAligned
import InitECandidate.Runtime.OriginalScratchAllocationCode
import InitECandidate.Runtime.PanSingleWordLookup
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Expose the exact successful scratch declaration and its real continuation,
with both actual allocation guards, all memory unchanged, and the sole global
frontier update. No minimum fuel or caller-space premise is needed. -/
theorem scratch_declaration_returned_contract {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (argument : ExpHOL 64) (tail : ProgHOL 64) (pointer size frame : BitVec 64) (value : ValueHOL 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [argument]=some [.val (.word size)])
 (scratchGlobal : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word pointer)))
 (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)))
 (ordered : frame≤pointer) (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.decCall name .one (ofString "scratch_alloc") [argument] tail)=(some (.returned value),post)) :
 ∃allocationPost output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (setVarHOLFinite name (.val (.word (scratchAllocationEnd pointer size))) {allocationPost with locals:=s.locals}) tail=
  (some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧
 allocationPost.memory=s.memory ∧allocationPost.memaddrs=s.memaddrs ∧allocationPost.be=s.be ∧allocationPost.code=s.code ∧
 allocationPost.globals=s.globals.update (ofString "scratch_ptr",.val (.word (scratchAllocationEnd pointer size))) ∧
 frame.toNat≤(scratchAllocationEnd pointer size).toNat ∧
 (scratchAllocationEnd pointer size).toNat+size.toNat≤pointer.toNat := by
 have installed : s.code.lookup (ofString "scratch_alloc")=
  some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_scratch_alloc,.one) := by
  rw [code];exact originalRuntimeCode_scratchAllocation_lookup
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=HolFiniteMapExact.empty.update (ofString "n",.val (.word size))
 have lookup:=pan_single_word_lookup s.code.lookup (ofString "scratch_alloc") (ofString "n")
  (sourceFunctionBody Guest.guestFn_scratch_alloc) size installed
 obtain ⟨allocated,allocationPost,output,allocationRun,checked,tailRun,postEq⟩:=
  evaluate_decCall_checked_returned_exact_scope s post name (ofString "scratch_alloc") .one .one _ _ _ _ callee value args lookup run
 let entry:=callEntryStateHOLFinite s callee
 have atSize : entry.locals.lookup (ofString "n")=some (.val (.word size)) := by
  simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 obtain ⟨returned,global,lower,extent,memory,domain,endian,installedKept⟩:=
  scratch_allocation_returned_progress_any_clock entry allocationPost pointer size frame allocated scratchGlobal atSize frameGlobal ordered code allocationRun
 have globals:=scratch_allocation_returned_globals_any_clock entry allocationPost pointer size frame allocated scratchGlobal atSize frameGlobal ordered code allocationRun
 subst allocated
 exact ⟨allocationPost,output,tailRun,postEq,memory,domain,endian,installedKept,globals,lower,extent⟩
#print axioms scratch_declaration_returned_contract
end InitECandidate.Runtime
