import InitECandidate.Runtime.HtabGrowRehash
import InitECandidate.Runtime.AllocationRound
import InitECandidate.Runtime.PanSingleWordLookup
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Expose the exact successful heap declaration and its real continuation,
with both actual allocation guards, all memory unchanged, and the sole global
frontier update. No minimum fuel or caller-space premise is needed. -/
theorem heap_declaration_returned_contract {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (argument : ExpHOL 64) (tail : ProgHOL 64) (pointer size : BitVec 64) (value : ValueHOL 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [argument]=some [.val (.word size)])
 (heapGlobal : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.decCall name .one (ofString "alloc") [argument] tail)=(some (.returned value),post)) :
 ∃allocationPost output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (setVarHOLFinite name (.val (.word (pointer))) {allocationPost with locals:=s.locals}) tail=
  (some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧
 allocationPost.memory=s.memory ∧allocationPost.memaddrs=s.memaddrs ∧allocationPost.be=s.be ∧allocationPost.code=s.code ∧
 allocationPost.globals=s.globals.update (ofString "heap_ptr",.val (.word (allocationEnd pointer size))) ∧
 size≤(33806089496 : BitVec 64)-pointer ∧(allocationEnd pointer size).toNat≤33806089496 := by
 have installed : s.code.lookup (ofString "alloc")=
  some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_alloc,.one) := by
  rw [code];exact originalRuntimeCode_allocation_lookup
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=HolFiniteMapExact.empty.update (ofString "n",.val (.word size))
 have lookup:=pan_single_word_lookup s.code.lookup (ofString "alloc") (ofString "n")
  (sourceFunctionBody Guest.guestFn_alloc) size installed
 obtain ⟨allocated,allocationPost,output,allocationRun,checked,tailRun,postEq⟩:=
  evaluate_decCall_checked_returned_exact_scope s post name (ofString "alloc") .one .one _ _ _ _ callee value args lookup run
 let entry:=callEntryStateHOLFinite s callee
 have atSize : entry.locals.lookup (ofString "n")=some (.val (.word size)) := by
  simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 obtain ⟨request,finish,returned,memory,domain,endian,installedKept,globals⟩:=
  alloc_body_returned entry allocationPost pointer size code heapGlobal atSize allocated allocationRun
 subst allocated
 exact ⟨allocationPost,output,tailRun,postEq,memory,domain,endian,installedKept,globals,request,finish⟩
#print axioms heap_declaration_returned_contract
end InitECandidate.Runtime
