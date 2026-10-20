import InitECandidate.Runtime.SplitExtensionReturnedWorld
import InitECandidate.Runtime.SplitExtensionWordLookup
import InitECandidate.Runtime.PanDecCallCheckedNormalExactScope
import InitECandidate.Runtime.TriePayloadWords
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A real original splitter declaration call exposes the new branch and
all returned-world/path facts to its caller. Stored old segment and child
words derive from the allocated source state, rather than a callee oracle. -/
theorem split_extension_declaration_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (name : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier node segmentLength key length matched value valueLength : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier) (short : length.toNat≤18)
 (extension : node∈extensions)
 (memoryLength : s.memory (node+40#64)=.word segmentLength)
 (inside : matched.toNat<segmentLength.toNat) (matchedBound : matched.toNat≤length.toNat)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=
  some [.val (.word node),.val (.word key),.val (.word length),.val (.word value),.val (.word valueLength),.val (.word matched)])
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 51≤s.clock)
 (run : evaluateHOLFiniteState s (.decCall name .one (ofString "_split_extension") arguments tail)=(none,post)) :
 ∃bodyPost output : PanSemStateFiniteExact 64 F,
 ∃larger newExtensions : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 insert frontier live⊆larger ∧extensions⊆newExtensions ∧
 AllocatedTrieWorld bodyPost larger newExtensions (insert frontier branches) newSize finish ∧
 TrieNodeKinds bodyPost larger newExtensions (insert frontier branches) ∧
 TrieNodePaths bodyPost larger newExtensions (insert frontier branches) newSize finish ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer bodyPost larger newSize nib len finish) ∧
 bodyPost.memaddrs=s.memaddrs ∧bodyPost.be=s.be ∧bodyPost.code=s.code ∧
 evaluateHOLFiniteState (setVarHOLFinite name (.val (.word frontier)) {bodyPost with locals:=s.locals}) tail=(none,output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} := by
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
 obtain ⟨returned,bodyPost,output,bodyRun,checked,tailRun,scope⟩:=evaluate_decCall_checked_normal_exact_scope s post name
  (ofString "_split_extension") .one .one arguments _ _ tail callee args lookup run
 have entryWorld : AllocatedTrieWorld entry live extensions branches size frontier:=world.after_memory_globals rfl rfl
 have entryKinds : TrieNodeKinds entry live extensions branches:=
  kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive (by intro current member;rfl)
 obtain ⟨valueEq,larger,newExtensions,newSize,finish,sub,extSub,worldOut,kindsOut,pathsOut,transport⟩:=
  split_extension_returned_world entry bodyPost live extensions branches size frontier node segment segmentLength key length matched child
   value valueLength entryWorld entryKinds (paths.after_context rfl rfl rfl) (keyPath.after_context rfl rfl rfl)
   short inside matchedBound extension
   (by simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   memoryKey memoryLength memoryChild
   (by simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   fullDomain code (by change 50≤s.clock-1;omega) returned bodyRun
 have metadata:=evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn__split_extension)
 rw [bodyRun] at metadata
 rw [valueEq] at tailRun
 refine ⟨bodyPost,output,larger,newExtensions,newSize,finish,sub,extSub,worldOut,kindsOut,pathsOut,?_,metadata.2.1,metadata.2.2.1,metadata.1,tailRun,scope⟩
 intro nib len path
 exact transport nib len (path.after_context rfl rfl rfl)

#print axioms split_extension_declaration_world
end InitECandidate.Runtime
