import InitECandidate.Runtime.NodeNewExtBodyReturnedWorld
import InitECandidate.Runtime.PanAssignmentCallNormalContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual installed node_new_ext assignment call exposes its newly allocated live
extension with the whole concrete trie and every existing path preserved. -/
theorem node_new_ext_assignment_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (pointer nib length child : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size pointer)
 (keyPath : TriePathBuffer s live size nib length pointer) (short : length.toNat≤18)
 (nonzero : length≠0) (childValid : child=0∨child∈live)
 (name : MlS) (arguments : List (ExpHOL 64))
 (args : evalListHOLFinite s (h:=fun address=>Classical.propDecidable (s.memaddrs address)) arguments=
  some [.val (.word nib),.val (.word length),.val (.word child)])
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.call (some (some (.local,name),none)) (ofString "node_new_ext") arguments)=(none,post)) :
 post.locals.lookup name=some (.val (.word pointer)) ∧
 AllocatedTrieWorld post (insert pointer live) (insert pointer extensions) branches
  (Function.update size pointer 56) (allocationEnd pointer 56) ∧
 TrieNodeKinds post (insert pointer live) (insert pointer extensions) branches ∧
 TrieNodePaths post (insert pointer live) (insert pointer extensions) branches
  (Function.update size pointer 56) (allocationEnd pointer 56) ∧
 (∀key len,TriePathBuffer s live size key len pointer→
  TriePathBuffer post (insert pointer live) (Function.update size pointer 56) key len (allocationEnd pointer 56)) ∧
 (∀other : MlS,other≠name→post.locals.lookup other=s.locals.lookup other) := by
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=
  ((HolFiniteMapExact.empty.update (ofString "nib",.val (.word nib))).update (ofString "nlen",.val (.word length))).update
   (ofString "child",.val (.word child))
 have installed : s.code.lookup (ofString "node_new_ext")=some
  ([(ofString "nib",.one),(ofString "nlen",.one),(ofString "child",.one)],sourceFunctionBody Guest.guestFn_node_new_ext,.one) := by
  rw [code];exact originalRuntimeCode_nodeNewExt_lookup
 have lookup:=pan_three_word_lookup s.code.lookup (ofString "node_new_ext")
  (ofString "nib") (ofString "nlen") (ofString "child") (sourceFunctionBody Guest.guestFn_node_new_ext)
  nib length child (by decide) (by decide) (by decide) installed
 obtain ⟨value,output,bodyRun,scope⟩:=assignment_call_normal_context s post .local name
  (ofString "node_new_ext") arguments _ (sourceFunctionBody Guest.guestFn_node_new_ext) callee .one args lookup run
 let entry:=callEntryStateHOLFinite s callee
 have entryWorld : AllocatedTrieWorld entry live extensions branches size pointer:=world.after_memory_globals rfl rfl
 have entryKinds : TrieNodeKinds entry live extensions branches:=
  kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive (by intro node member;rfl)
 obtain ⟨returned,worldOut,kindsOut,pathsOut,transport⟩:=node_new_ext_body_returned_world entry output
  live extensions branches size pointer nib length child entryWorld entryKinds
  (paths.after_context rfl rfl rfl) (keyPath.after_context rfl rfl rfl) short nonzero childValid
  (by simp (config:={decide:=true}) [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE])
  (by simp (config:={decide:=true}) [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE])
  (by simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE])
  fullDomain code value bodyRun
 subst post
 refine ⟨?_,worldOut.after_memory_globals rfl rfl,?_,pathsOut.after_context rfl rfl rfl,?_,?_⟩
 · simp [returned,setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · exact kindsOut.after_kind_frame worldOut.layout.extensionLive worldOut.layout.branchLive (by intro node member;rfl)
 · intro key len path
   exact (transport key len (path.after_context rfl rfl rfl)).after_context rfl rfl rfl

 · intro other different
   simp [setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different]

#print axioms node_new_ext_assignment_world
end InitECandidate.Runtime
