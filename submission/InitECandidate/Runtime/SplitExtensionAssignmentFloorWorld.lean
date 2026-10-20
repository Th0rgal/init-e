import InitECandidate.Runtime.SplitExtensionReturnedFloorWorld
import InitECandidate.Runtime.SplitExtensionWordLookup
import InitECandidate.Runtime.PanAssignmentCallNormalContext
import InitECandidate.Runtime.TriePayloadWords
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A real original splitter assignment call exposes the new branch and
all returned-world/path facts to its caller. Stored old segment and child
words derive from the allocated source state, rather than a callee oracle. -/
theorem split_extension_assignment_floor_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (name : MlS) (arguments : List (ExpHOL 64))
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier node segmentLength key length matched value valueLength : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier) (short : length.toNat≤18)
 (floor : Nat) (lower : TrieAllocationFloor s live branches floor)
 (heapAbove : floor≤frontier.toNat) (keyAbove : floor≤key.toNat)
 (extension : node∈extensions)
 (memoryLength : s.memory (node+40#64)=.word segmentLength)
 (inside : matched.toNat<segmentLength.toNat) (matchedBound : matched.toNat≤length.toNat)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=
  some [.val (.word node),.val (.word key),.val (.word length),.val (.word value),.val (.word valueLength),.val (.word matched)])
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 51≤s.clock)
 (run : evaluateHOLFiniteState s (.call (some (some (.local,name),none)) (ofString "_split_extension") arguments)=(none,post)) :
 post.locals.lookup name=some (.val (.word frontier)) ∧
 ∃larger newExtensions : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 insert frontier live⊆larger ∧extensions⊆newExtensions ∧
 AllocatedTrieWorld post larger newExtensions (insert frontier branches) newSize finish ∧
 TrieNodeKinds post larger newExtensions (insert frontier branches) ∧
 TrieNodePaths post larger newExtensions (insert frontier branches) newSize finish ∧
 TrieAllocationFloor post larger (insert frontier branches) floor ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) ∧
 (∀other : MlS,other≠name→post.locals.lookup other=s.locals.lookup other) := by
 have nodeLive : node∈live:=world.layout.extensionLive extension
 have nonBranch : node∉branches:=fun branch=>Set.disjoint_left.mp world.layout.differentKinds extension branch
 obtain ⟨segment,storedLength,memoryKey,lengthAt,storedShort,storedPath⟩:=paths.paths node nodeLive nonBranch
 obtain ⟨child,memoryChild⟩:=source_memory_word s (node+48#64)
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=
  ((((((HolFiniteMapExact.empty.update (ofString "node",.val (.word node))).update (ofString "rk",.val (.word key))).update (ofString "rl",.val (.word length))).update (ofString "vptr",.val (.word value))).update (ofString "vlen",.val (.word valueLength))).update (ofString "pl",.val (.word matched)))
 let entry:=callEntryStateHOLFinite s callee
 have lookup : lookupCodeHOLFinite s.code.lookup (ofString "_split_extension")
  [.val (.word node),.val (.word key),.val (.word length),.val (.word value),.val (.word valueLength),.val (.word matched)]=
  some (sourceFunctionBody Guest.guestFn__split_extension,callee,.one) := by
  rw [code];exact original_split_extension_word_lookup node key length value valueLength matched
 obtain ⟨returned,bodyPost,bodyRun,postEq⟩:=assignment_call_normal_context s post .local name
  (ofString "_split_extension") arguments _ _ callee .one args lookup run
 have entryWorld : AllocatedTrieWorld entry live extensions branches size frontier:=world.after_memory_globals rfl rfl
 have entryKinds : TrieNodeKinds entry live extensions branches:=
  kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive (by intro current member;rfl)
 obtain ⟨valueEq,larger,newExtensions,newSize,finish,sub,extSub,worldOut,kindsOut,pathsOut,lowerOut,transport⟩:=
  split_extension_returned_floor_world entry bodyPost live extensions branches size frontier node segment segmentLength key length matched child
   value valueLength entryWorld entryKinds (paths.after_context rfl rfl rfl) (keyPath.after_context rfl rfl rfl)
   short inside matchedBound floor (lower.after_memory rfl) heapAbove keyAbove extension
   (by simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   memoryKey memoryLength memoryChild
   (by simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   fullDomain code (by change 50≤s.clock-1;omega) returned bodyRun
 have postMemory : post.memory=bodyPost.memory:=by rw [postEq];rfl
 have postGlobals : post.globals=bodyPost.globals:=by rw [postEq];rfl
 have postDomains : post.memaddrs=bodyPost.memaddrs:=by rw [postEq];rfl
 have postEndian : post.be=bodyPost.be:=by rw [postEq];rfl
 refine ⟨?_,larger,newExtensions,newSize,finish,sub,extSub,
  worldOut.after_memory_globals postMemory postGlobals,?_,pathsOut.after_context postMemory postDomains postEndian,lowerOut.after_memory postMemory,?_,?_⟩
 · rw [postEq]
   simp [valueEq,setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · exact kindsOut.after_kind_frame worldOut.layout.extensionLive worldOut.layout.branchLive
    (by intro current member;rw [postMemory])
 · intro nib len path
   exact (transport nib len (path.after_context rfl rfl rfl)).after_context postMemory postDomains postEndian
 · intro other different
   rw [postEq]
   simp [setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different]

#print axioms split_extension_assignment_floor_world
end InitECandidate.Runtime
