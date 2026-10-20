import InitECandidate.Runtime.MptInsertIndexedBodyReturnedWorld
import InitECandidate.Runtime.MptInsertIndexedLookup
import InitECandidate.Runtime.PanAssignmentCallNormalContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual installed six-argument insertion assignment returns its root
and enlarged path-preserving world, using the original callee and caller scope. -/
theorem mpt_insert_indexed_assignment_world {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
 (arguments : List (ExpHOL 64)) (name : MlS)
 (frontier node key length level valuePointer valueLength : BitVec 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=
  some [.val (.word node),.val (.word key),.val (.word length),.val (.word level),.val (.word valuePointer),.val (.word valueLength)])
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (nodeValid : node=0 ∨node∈live)
 (inside : level.toNat≤length.toNat)
 (capacity : ∀node∈live,32≤size node) (recordsBefore : ∀node∈live,node.toNat+32≤key.toNat)
 (aligned : key.toNat%8=0) (keyExtent : key.toNat+length.toNat≤33806089496) (short : length.toNat≤18)
 (code : s.code=originalRuntimeCode) (budget : 19*((2^64+203)+1)+1≤s.clock)
 (run : evaluateHOLFiniteState s (.call (some (some (.local,name),none)) (ofString "_mpt_insert_node") arguments)=(none,post)) :
 ∃root : BitVec 64,∃larger newExtensions newBranches : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 post.locals.lookup name=some (.val (.word root)) ∧(root=0 ∨root∈larger) ∧live⊆larger ∧extensions⊆newExtensions ∧branches⊆newBranches ∧
 AllocatedTrieWorld post larger newExtensions newBranches newSize finish ∧
 TrieNodeKinds post larger newExtensions newBranches ∧TrieNodePaths post larger newExtensions newBranches newSize finish ∧
 TriePathBuffer post larger newSize key length finish ∧
 (∀other : MlS,other≠name→post.locals.lookup other=s.locals.lookup other) := by
 have lookup:=mpt_insert_indexed_lookup s node key length level valuePointer valueLength code
 obtain ⟨value,output,bodyRun,scope⟩:=assignment_call_normal_context s post .local name
  (ofString "_mpt_insert_node") arguments _ (sourceFunctionBody Guest.guestFn__mpt_insert_node)
  (mptInsertCalleeLocals node key length level valuePointer valueLength) .one args lookup run
 let entry:=callEntryStateHOLFinite s (mptInsertCalleeLocals node key length level valuePointer valueLength)
 have entryWorld : AllocatedTrieWorld entry live extensions branches size frontier:=world.after_memory_globals rfl rfl
 have entryKinds : TrieNodeKinds entry live extensions branches:=
  kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive (by intro current member;rfl)
 obtain ⟨root,larger,newExtensions,newBranches,newSize,finish,returned,valid,sub,extSub,branchSub,
  worldOut,kindsOut,pathsOut,keyOut⟩:=
  mpt_insert_indexed_body_returned_world entry output live extensions branches size frontier node key length level valuePointer valueLength
   entryWorld entryKinds (paths.after_context rfl rfl rfl) (keyPath.after_context rfl rfl rfl) fullDomain nodeValid
   (by simp (config:={decide:=true}) [entry,callEntryStateHOLFinite,mptInsertCalleeLocals,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp (config:={decide:=true}) [entry,callEntryStateHOLFinite,mptInsertCalleeLocals,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp (config:={decide:=true}) [entry,callEntryStateHOLFinite,mptInsertCalleeLocals,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp (config:={decide:=true}) [entry,callEntryStateHOLFinite,mptInsertCalleeLocals,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp (config:={decide:=true}) [entry,callEntryStateHOLFinite,mptInsertCalleeLocals,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp (config:={decide:=true}) [entry,callEntryStateHOLFinite,mptInsertCalleeLocals,HolFiniteMapExact.lookup_update,FUPDATE])
   inside capacity recordsBefore aligned keyExtent short code (by change 19*((2^64+203)+1)≤s.clock-1;omega) value bodyRun
 subst post
 refine ⟨root,larger,newExtensions,newBranches,newSize,finish,?_,valid,sub,extSub,branchSub,
  worldOut.after_memory_globals rfl rfl,?_,pathsOut.after_context rfl rfl rfl,keyOut.after_context rfl rfl rfl,?_⟩
 · simp [returned,setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · exact kindsOut.after_kind_frame worldOut.layout.extensionLive worldOut.layout.branchLive (by intro current member;rfl)
 · intro other different
   simp [setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different]

#print axioms mpt_insert_indexed_assignment_world
end InitECandidate.Runtime
