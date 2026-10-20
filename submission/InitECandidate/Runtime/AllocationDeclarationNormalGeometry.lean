import InitECandidate.Runtime.AllocationDeclarationReturned
import InitECandidate.Runtime.PanDecCallNormalGlobalMemoryClockScope
import InitECandidate.Runtime.HtabGrowRehash
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- A real normal allocator declaration supplies its own successful guard and
exact resumed context, without a room or accessibility premise. -/
theorem allocation_declaration_normal_geometry {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (argument : ExpHOL 64) (tail : ProgHOL 64) (heap size : BitVec 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [argument]=some [.val (.word size)])
 (code : s.code=originalRuntimeCode) (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (heapBound : heap.toNat≤33806089496)
 (run : evaluateHOLFiniteState s (.decCall name .one (ofString "alloc") [argument] tail)=(none,post)) :
 ∃ready output : PanSemStateFiniteExact 64 F,
  evaluateHOLFiniteState ready tail=(none,output) ∧ready.locals=s.locals.update (name,.val (.word heap)) ∧
  ready.memory=s.memory ∧ready.code=s.code ∧ready.memaddrs=s.memaddrs ∧ready.clock=s.clock-1 ∧
  ready.globals=(setGlobalHOLFinite (ofString "heap_ptr") (.val (.word (allocationEnd heap size))) s).globals ∧
  heap.toNat+size.toNat≤(allocationEnd heap size).toNat ∧(allocationEnd heap size).toNat≤33806089496 ∧
  post.memory=output.memory := by
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=HolFiniteMapExact.empty.update (ofString "n",.val (.word size))
 have lookup:=pan_single_word_lookup s.code.lookup (ofString "alloc") (ofString "n") (sourceFunctionBody Guest.guestFn_alloc) size
  (by rw [code];exact originalRuntimeCode_allocation_lookup)
 obtain ⟨value,bodyPost,_,_,bodyRun,_,_,_,_,_,_,_,_,_⟩ := evaluate_decCall_normal_global_memory_clock_scope s post name (ofString "alloc")
  .one .one [argument] [.val (.word size)] (sourceFunctionBody Guest.guestFn_alloc) tail callee args lookup run
 obtain ⟨request,within,_,_,_,_,_,_⟩:=alloc_body_returned (callEntryStateHOLFinite s callee) bodyPost heap size code atHeap
  (by simp [callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) value bodyRun
 have ticks : s.clock≠0 := by
  intro zero
  rw [evaluateHOLFiniteState_decCall_total,args] at run
  simp [zero] at run
  split at run <;>simp at run
 obtain ⟨allocated,_,clock,memory,locals,installed,domain,_,_,globals,declaration⟩:=
  evaluate_alloc_call_and_declaration s argument heap size args code ticks atHeap request within
 rw [declaration name tail] at run
 let ready:=setVarHOLFinite name (.val (.word heap)) allocated
 change (let output:=evaluateHOLFiniteState ready tail;(output.1,{output.2 with locals:=HolFiniteMapExact.resVarEq output.2.locals (name,s.locals.lookup name)}))=(none,post) at run
 cases tailRun : evaluateHOLFiniteState ready tail with
 | mk result output=>
  rw [tailRun] at run
  have resultEq:=(Prod.mk.inj run).1
  change result=none at resultEq
  subst result
  have postEq:=(Prod.mk.inj run).2
  refine ⟨ready,output,tailRun,?_,memory,installed,domain,clock,globals,
   (allocationEnd_covers heap size (allocationGuard_sum_bound heap size heapBound request)).1,within,?_⟩
  · change allocated.locals.update _=_;rw [locals]
  · rw [←postEq]
#print axioms allocation_declaration_normal_geometry
end InitECandidate.Runtime
