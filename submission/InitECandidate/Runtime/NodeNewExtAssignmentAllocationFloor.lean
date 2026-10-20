import InitECandidate.Runtime.NodeNewExtBodyAllocationFloor
import InitECandidate.Runtime.PanAssignmentCallNormalContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual installed extension assignment call preserves the allocation floor through callee entry and caller scope restoration. -/
theorem node_new_ext_assignment_allocation_floor {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (pointer nib length child : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size pointer)
 (keyPath : TriePathBuffer s live size nib length pointer) (short : length.toNat≤18)
 (floor : Nat) (lower : TrieAllocationFloor s live branches floor)
 (heapAbove : floor≤pointer.toNat) (keyAbove : floor≤nib.toNat)
 (nonzero : length≠0) (childValid : child=0∨child∈live)
 (name : MlS) (arguments : List (ExpHOL 64))
 (args : evalListHOLFinite s (h:=fun address=>Classical.propDecidable (s.memaddrs address)) arguments=
  some [.val (.word nib),.val (.word length),.val (.word child)])
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.call (some (some (.local,name),none)) (ofString "node_new_ext") arguments)=(none,post)) :
 TrieAllocationFloor post (insert pointer live) branches floor := by
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
 have lowerOut:=node_new_ext_body_returned_allocation_floor entry output
  live extensions branches size pointer nib length child entryWorld entryKinds
  (paths.after_context rfl rfl rfl) (keyPath.after_context rfl rfl rfl) short floor (lower.after_memory rfl) heapAbove keyAbove nonzero childValid
  (by simp (config:={decide:=true}) [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE])
  (by simp (config:={decide:=true}) [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE])
  (by simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE])
  fullDomain code value bodyRun
 subst post
 exact lowerOut.after_memory rfl

#print axioms node_new_ext_assignment_allocation_floor
end InitECandidate.Runtime
