import InitECandidate.Runtime.NodeNewLeafRegistryReach
import InitECandidate.Runtime.PanAssignmentCallNormalContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The real assignment call used by insertion establishes the same fresh
leaf fields and traversal registry as the declaration call. Every fact is
derived from this actual normally completed call, at its original clock. -/
theorem node_new_leaf_assignment_ready {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (arguments : List (ExpHOL 64))
 (pointer nib length valuePointer valueLength : BitVec 64) (live extensions branches : Set (BitVec 64))
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=
  some [.val (.word nib),.val (.word length),.val (.word valuePointer),.val (.word valueLength)])
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (capped : pointer.toNat≤33806089496)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (registry : TrieWalkRegistry live extensions branches s)
 (ownedBelow : ∀address,TrieWalkRegistryWord live extensions branches address→address.toNat<pointer.toNat)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.call (some (some (.local,name),none)) (ofString "node_new_leaf") arguments)=(none,post)) :
 NodeNewLeafDeclarationReady s post name pointer nib length valuePointer valueLength live extensions branches := by
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=
  (((HolFiniteMapExact.empty.update (ofString "nib",.val (.word nib))).update (ofString "nlen",.val (.word length))).update
   (ofString "vptr",.val (.word valuePointer))).update (ofString "vlen",.val (.word valueLength))
 let entry:=callEntryStateHOLFinite s callee
 have installed : s.code.lookup (ofString "node_new_leaf")=some
  ([(ofString "nib",.one),(ofString "nlen",.one),(ofString "vptr",.one),(ofString "vlen",.one)],sourceFunctionBody Guest.guestFn_node_new_leaf,.one) := by
  rw [code];exact originalRuntimeCode_nodeNewLeaf_lookup
 have lookup:=pan_four_word_lookup s.code.lookup (ofString "node_new_leaf")
  (ofString "nib") (ofString "nlen") (ofString "vptr") (ofString "vlen") (sourceFunctionBody Guest.guestFn_node_new_leaf)
  nib length valuePointer valueLength (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) installed
 obtain ⟨value,bodyPost,bodyRun,postEq⟩:=assignment_call_normal_context s post .local name (ofString "node_new_leaf")
  arguments _ _ callee .one args lookup run
 obtain ⟨returned,kind,nibAt,lengthAt,valueAt,valueLengthAt,globals,extent,finish,aligned,memory,domain,endian,keptCode⟩:=
  node_new_leaf_returned_context entry bodyPost pointer nib length valuePointer valueLength value
   (by simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   atHeap capped fullDomain code bodyRun
 have older:=registry.after_word_frame (fun address owned=>memory address (ownedBelow address owned))
 have registered:=TrieWalkRegistry.insert_terminal bodyPost live extensions branches pointer 1 older kind (Or.inr rfl)
 rw [postEq]
 refine ⟨?_,?_,kind,nibAt,lengthAt,valueAt,valueLengthAt,globals,extent,finish,aligned,memory,domain,endian,keptCode,registered.after_memory rfl⟩
 · simp [returned,setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · intro key different
   simp [setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]

#print axioms node_new_leaf_assignment_ready
end InitECandidate.Runtime
