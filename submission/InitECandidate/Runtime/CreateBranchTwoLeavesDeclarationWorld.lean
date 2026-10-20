import InitECandidate.Runtime.CreateBranchTwoLeavesWorld
import InitECandidate.Runtime.CreateBranchTwoLeavesLookup
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual original eight-argument branch-constructor declaration reaches its
source continuation with the fresh branch and whole trie world. The original
body supplies the returned value, allocation, stored paths and clock bound. -/
theorem create_branch_two_leaves_declaration_returned_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier k1 l1 v1 vl1 k2 l2 v2 vl2 : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (path1 : TriePathBuffer s live size k1 l1 frontier) (short1 : l1.toNat≤18)
 (path2 : TriePathBuffer s live size k2 l2 frontier) (short2 : l2.toNat≤18)
 (name : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64)
 (args : evalListHOLFinite s (h:=fun address=>Classical.propDecidable (s.memaddrs address)) arguments=
  some [.val (.word k1),.val (.word l1),.val (.word v1),.val (.word vl1),
   .val (.word k2),.val (.word l2),.val (.word v2),.val (.word vl2)])
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 51≤s.clock) (returned : ValueHOL 64)
 (run : evaluateHOLFiniteState s (.decCall name .one (ofString "_create_branch_from_two_leaves") arguments tail)=
  (some (.returned returned),post)) :
 ∃ready output : PanSemStateFiniteExact 64 F,∃larger : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 ready.locals.lookup name=some (.val (.word frontier)) ∧
 (∀key,key≠name→ ready.locals.lookup key=s.locals.lookup key) ∧
 s.clock≤ready.clock+51 ∧ready.clock≤s.clock ∧ready.code=s.code ∧ready.memaddrs=s.memaddrs ∧ready.be=s.be ∧
 insert frontier live⊆larger ∧AllocatedTrieWorld ready larger extensions (insert frontier branches) newSize finish ∧
 TrieNodeKinds ready larger extensions (insert frontier branches) ∧
 TrieNodePaths ready larger extensions (insert frontier branches) newSize finish ∧
 (∀key len,TriePathBuffer s live size key len frontier→TriePathBuffer ready larger newSize key len finish) ∧
 evaluateHOLFiniteState ready tail=(some (.returned returned),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} := by
 let callee:=createBranchTwoLeavesLocals k1 l1 v1 vl1 k2 l2 v2 vl2
 let entry:=callEntryStateHOLFinite s callee
 have lookup:=create_branch_two_leaves_lookup s k1 l1 v1 vl1 k2 l2 v2 vl2 code
 obtain ⟨value,bodyPost,output,bodyRun,checked,tailRun,scope⟩:=evaluate_decCall_checked_returned_exact_scope s post
  name (ofString "_create_branch_from_two_leaves") .one .one arguments _
  (sourceFunctionBody Guest.guestFn__create_branch_from_two_leaves) tail callee returned args lookup run
 have entryWorld : AllocatedTrieWorld entry live extensions branches size frontier:=world.after_memory_globals rfl rfl
 have entryKinds : TrieNodeKinds entry live extensions branches:=
  kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive (by intro node member;rfl)
 obtain ⟨valueEq,larger,newSize,finish,sub,worldOut,kindsOut,pathsOut,transport⟩:=
  create_branch_two_leaves_returned_world entry bodyPost live extensions branches size
   frontier k1 l1 v1 vl1 k2 l2 v2 vl2 entryWorld entryKinds (paths.after_context rfl rfl rfl)
   (path1.after_context rfl rfl rfl) short1 (path2.after_context rfl rfl rfl) short2
   (by simp (config:={decide:=true}) [entry,callEntryStateHOLFinite,callee,createBranchTwoLeavesLocals,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp (config:={decide:=true}) [entry,callEntryStateHOLFinite,callee,createBranchTwoLeavesLocals,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp (config:={decide:=true}) [entry,callEntryStateHOLFinite,callee,createBranchTwoLeavesLocals,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp (config:={decide:=true}) [entry,callEntryStateHOLFinite,callee,createBranchTwoLeavesLocals,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp (config:={decide:=true}) [entry,callEntryStateHOLFinite,callee,createBranchTwoLeavesLocals,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp (config:={decide:=true}) [entry,callEntryStateHOLFinite,callee,createBranchTwoLeavesLocals,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp (config:={decide:=true}) [entry,callEntryStateHOLFinite,callee,createBranchTwoLeavesLocals,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp [entry,callEntryStateHOLFinite,callee,createBranchTwoLeavesLocals,HolFiniteMapExact.lookup_update,FUPDATE])
   fullDomain code (by change 50≤s.clock-1;omega) value bodyRun
 subst value
 let ready:=setVarHOLFinite name (.val (.word frontier)) {bodyPost with locals:=s.locals}
 have metadata:=evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn__create_branch_from_two_leaves)
 rw [bodyRun] at metadata
 have counted : RunBounded entry (sourceFunctionBody Guest.guestFn__create_branch_from_two_leaves) 50:=RunBounded.ofProg create_branch_two_leaves_body_bounded code (by change 50≤s.clock-1;omega)
 unfold RunBounded at counted
 rw [bodyRun] at counted
 dsimp only at counted
 refine ⟨ready,output,larger,newSize,finish,?_,?_,?_,?_,metadata.1,metadata.2.1,metadata.2.2.1,sub,
  worldOut.after_memory_globals rfl rfl,?_,pathsOut.after_context rfl rfl rfl,?_,tailRun,scope⟩
 · simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · intro key separate
   simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm separate]
 · change s.clock≤bodyPost.clock+51
   have spent:=counted.1
   change s.clock-1≤bodyPost.clock+50 at spent
   omega
 · change bodyPost.clock≤s.clock
   have smaller:=counted.2.1
   change bodyPost.clock≤s.clock-1 at smaller
   omega
 · exact kindsOut.after_kind_frame worldOut.layout.extensionLive worldOut.layout.branchLive (by intro node member;rfl)
 · intro key len path
   exact (transport key len (path.after_context rfl rfl rfl)).after_context rfl rfl rfl

#print axioms create_branch_two_leaves_declaration_returned_world
end InitECandidate.Runtime
