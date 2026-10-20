import InitECandidate.Runtime.MptInsertLeafReturnedWorld
import InitECandidate.Runtime.OriginalInsertIntoLeafCode
import InitECandidate.Runtime.PanFiveWordShapeLookup
import InitECandidate.Runtime.PanAssignmentCallNormalContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original leaf insertion assignment call exposes the actual returned
world to its caller, including its assigned live root and restored locals. -/
theorem mpt_insert_leaf_assignment_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (name : MlS) (arguments : List (ExpHOL 64))
 (frontier node key length value valueLength : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier) (short : length.toNat≤18)
 (nodeLive : node∈live) (nonExt : node∉extensions) (nonBranch : node∉branches)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=
  some [.val (.word node),.val (.word key),.val (.word length),.val (.word value),.val (.word valueLength)])
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 145≤s.clock)
 (run : evaluateHOLFiniteState s (.call (some (some (.local,name),none)) (ofString "_insert_into_leaf") arguments)=(none,post)) :
 ∃root : BitVec 64,∃larger newExtensions newBranches : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 post.locals.lookup name=some (.val (.word root)) ∧root∈larger ∧live⊆larger ∧extensions⊆newExtensions ∧branches⊆newBranches ∧
 AllocatedTrieWorld post larger newExtensions newBranches newSize finish ∧
 TrieNodeKinds post larger newExtensions newBranches ∧
 TrieNodePaths post larger newExtensions newBranches newSize finish ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) ∧
 (∀other : MlS,other≠name→post.locals.lookup other=s.locals.lookup other) := by
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=
  ((((HolFiniteMapExact.empty.update (ofString "node",.val (.word node))).update
   (ofString "rk",.val (.word key))).update (ofString "rl",.val (.word length))).update
   (ofString "vptr",.val (.word value))).update (ofString "vlen",.val (.word valueLength))
 let entry:=callEntryStateHOLFinite s callee
 have installed : s.code.lookup (ofString "_insert_into_leaf")=some
  ([(ofString "node",.one),(ofString "rk",.one),(ofString "rl",.one),(ofString "vptr",.one),(ofString "vlen",.one)],
   sourceFunctionBody Guest.guestFn__insert_into_leaf,.one) := by
  rw [code];exact originalRuntimeCode_insertIntoLeaf_lookup
 have lookup:=pan_five_word_shape_lookup s.code.lookup (ofString "_insert_into_leaf")
  (ofString "node") (ofString "rk") (ofString "rl") (ofString "vptr") (ofString "vlen")
  (sourceFunctionBody Guest.guestFn__insert_into_leaf) .one node key length value valueLength
  (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) installed
 obtain ⟨returned,bodyPost,bodyRun,postEq⟩:=assignment_call_normal_context s post .local name
  (ofString "_insert_into_leaf") arguments _ _ callee .one args lookup run
 have entryWorld : AllocatedTrieWorld entry live extensions branches size frontier:=world.after_memory_globals rfl rfl
 have entryKinds : TrieNodeKinds entry live extensions branches:=
  kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive (by intro current member;rfl)
 obtain ⟨root,larger,newExtensions,newBranches,newSize,finish,valueEq,rootLive,sub,extSub,branchSub,
  worldOut,kindsOut,pathsOut,transport⟩:=mpt_insert_leaf_returned_world entry bodyPost live extensions branches size
   frontier node key length value valueLength entryWorld entryKinds (paths.after_context rfl rfl rfl)
   (keyPath.after_context rfl rfl rfl) short nodeLive nonExt nonBranch
   (by simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   fullDomain code (by change 144≤s.clock-1;omega) returned bodyRun
 have postMemory : post.memory=bodyPost.memory:=by rw [postEq];rfl
 have postGlobals : post.globals=bodyPost.globals:=by rw [postEq];rfl
 have postDomains : post.memaddrs=bodyPost.memaddrs:=by rw [postEq];rfl
 have postEndian : post.be=bodyPost.be:=by rw [postEq];rfl
 refine ⟨root,larger,newExtensions,newBranches,newSize,finish,?_,rootLive,sub,extSub,branchSub,
  worldOut.after_memory_globals postMemory postGlobals,?_,pathsOut.after_context postMemory postDomains postEndian,?_,?_⟩
 · rw [postEq]
   simp [valueEq,setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · exact kindsOut.after_kind_frame worldOut.layout.extensionLive worldOut.layout.branchLive
    (by intro current member;rw [postMemory])
 · intro nib len path
   exact (transport nib len (path.after_context rfl rfl rfl)).after_context postMemory postDomains postEndian
 · intro other different
   rw [postEq]
   simp [setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different]

#print axioms mpt_insert_leaf_assignment_world
end InitECandidate.Runtime
