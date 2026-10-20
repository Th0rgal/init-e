import InitECandidate.Runtime.PanAssignmentCallNormalContext
import InitECandidate.Runtime.HtabGrowRehash
import InitECandidate.Runtime.AllocationBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem state_init_global_allocation_normal_geometry {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (argument : ExpHOL 64) (heap size : BitVec 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [argument]=some [.val (.word size)])
 (code : s.code=originalRuntimeCode) (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (bounded : heap.toNat≤33806089496) (different : name≠ofString "heap_ptr")
 (run : evaluateHOLFiniteState s (.call (some (some (.global,name),none)) (ofString "alloc") [argument])=(none,post)) :
 post.memory=s.memory ∧post.code=s.code ∧post.memaddrs=s.memaddrs ∧post.locals=s.locals ∧
 post.globals.lookup name=some (.val (.word heap)) ∧
 post.globals.lookup (ofString "heap_ptr")=some (.val (.word (allocationEnd heap size))) ∧
 (∀key,key≠name→key≠ofString "heap_ptr"→post.globals.lookup key=s.globals.lookup key) ∧
 heap.toNat+size.toNat≤(allocationEnd heap size).toNat ∧
 (allocationEnd heap size).toNat%8=0 ∧(allocationEnd heap size).toNat≤33806089496 := by
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=HolFiniteMapExact.empty.update (ofString "n",.val (.word size))
 have lookup:=pan_single_word_lookup s.code.lookup (ofString "alloc") (ofString "n") (sourceFunctionBody Guest.guestFn_alloc) size
  (by rw [code];exact originalRuntimeCode_allocation_lookup)
 obtain ⟨value,bodyPost,bodyRun,postEq⟩:=assignment_call_normal_context s post .global name (ofString "alloc") [argument]
  [.val (.word size)] (sourceFunctionBody Guest.guestFn_alloc) callee .one args lookup run
 obtain ⟨request,within,valueEq,memory,domain,endian,installed,globals⟩:=alloc_body_returned (callEntryStateHOLFinite s callee)
  bodyPost heap size code atHeap (by simp [callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) value bodyRun
 have covers:=allocationEnd_covers heap size (allocationGuard_sum_bound heap size bounded request)
 rw [postEq,valueEq]
 refine ⟨memory,installed,domain,rfl,?_,?_,?_,covers.1,covers.2.2,within⟩
 · simp [setKvarHOLFinite,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · simp [setKvarHOLFinite,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,globals]
 · intro key notName notHeap
   simp [setKvarHOLFinite,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,globals,Ne.symm notName,Ne.symm notHeap,callEntryStateHOLFinite]
#print axioms state_init_global_allocation_normal_geometry
end InitECandidate.Runtime
