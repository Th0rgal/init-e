import InitECandidate.Runtime.CreateBranchLeafSideWorld
import InitECandidate.Runtime.ReachesReturnedContinuation
import InitECandidate.Runtime.AllocationFramedGlobals
import InitECandidate.Runtime.HtabDelFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete actual two-leaf branch constructor returns its newly
allocated live branch with the whole allocated trie, exact kinds and stored
paths preserved. Both actual conditional leaf sides and their byte-selected
child stores are included, with no future-callee/frame/heap-room premise. -/
theorem create_branch_two_leaves_returned_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier k1 l1 v1 vl1 k2 l2 v2 vl2 : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (path1 : TriePathBuffer s live size k1 l1 frontier) (short1 : l1.toNat≤18)
 (path2 : TriePathBuffer s live size k2 l2 frontier) (short2 : l2.toNat≤18)
 (atK1 : s.locals.lookup (ofString "k1")=some (.val (.word k1)))
 (atL1 : s.locals.lookup (ofString "l1")=some (.val (.word l1)))
 (atV1 : s.locals.lookup (ofString "v1")=some (.val (.word v1)))
 (atVL1 : s.locals.lookup (ofString "vl1")=some (.val (.word vl1)))
 (atK2 : s.locals.lookup (ofString "k2")=some (.val (.word k2)))
 (atL2 : s.locals.lookup (ofString "l2")=some (.val (.word l2)))
 (atV2 : s.locals.lookup (ofString "v2")=some (.val (.word v2)))
 (atVL2 : s.locals.lookup (ofString "vl2")=some (.val (.word vl2)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 50≤s.clock) (returned : ValueHOL 64)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn__create_branch_from_two_leaves)=(some (.returned returned),post)) :
 returned=.val (.word frontier) ∧
 ∃larger : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 insert frontier live⊆larger ∧AllocatedTrieWorld post larger extensions (insert frontier branches) newSize finish ∧
 TrieNodeKinds post larger extensions (insert frontier branches) ∧TrieNodePaths post larger extensions (insert frontier branches) newSize finish ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) := by
 have metadata:=evaluateHOLFiniteState_metadata s (sourceFunctionBody Guest.guestFn__create_branch_from_two_leaves)
 rw [run] at metadata
 rw [sourceFunctionBody_eq_structural] at run
 change evaluateHOLFiniteState s (createBranchTwoLeavesAt 0)=_ at run
 have reached:=allocated_trie_branch_paths_reaches s (ofString "br") (createBranchTwoLeavesAt 1) frontier live extensions branches size world kinds paths fullDomain code (by omega)
 rw [← source_create_branch_two_leaves_0] at reached
 obtain ⟨ready,⟨branchReady,readyWorld,readyKinds,readyPaths⟩,spent,_,agreement,tailReturned⟩:=reaches_returned_continuation s _ _ _ 41 returned reached (by rw [run])
 let output:=(evaluateHOLFiniteState ready (createBranchTwoLeavesAt 1)).2
 have tail : evaluateHOLFiniteState ready (createBranchTwoLeavesAt 1)=(some (.returned returned),output):=Prod.ext tailReturned rfl
 have readyBudget : 9≤ready.clock:=by omega
 have readyK1 : ready.locals.lookup (ofString "k1")=some (.val (.word k1)) := (branchReady.locals _ (by decide)).trans atK1
 have readyL1 : ready.locals.lookup (ofString "l1")=some (.val (.word l1)) := (branchReady.locals _ (by decide)).trans atL1
 have readyV1 : ready.locals.lookup (ofString "v1")=some (.val (.word v1)) := (branchReady.locals _ (by decide)).trans atV1
 have readyVL1 : ready.locals.lookup (ofString "vl1")=some (.val (.word vl1)) := (branchReady.locals _ (by decide)).trans atVL1
 have readyK2 : ready.locals.lookup (ofString "k2")=some (.val (.word k2)) := (branchReady.locals _ (by decide)).trans atK2
 have readyL2 : ready.locals.lookup (ofString "l2")=some (.val (.word l2)) := (branchReady.locals _ (by decide)).trans atL2
 have readyV2 : ready.locals.lookup (ofString "v2")=some (.val (.word v2)) := (branchReady.locals _ (by decide)).trans atV2
 have readyVL2 : ready.locals.lookup (ofString "vl2")=some (.val (.word vl2)) := (branchReady.locals _ (by decide)).trans atVL2
 have readyDomain : ∀address : BitVec 64,address.toNat<33806089496→ ready.memaddrs address := by
  intro address small;rw [branchReady.domain];exact fullDomain address small
 have readyCode : ready.code=originalRuntimeCode:=branchReady.code.trans code
 have firstPath:=branchReady.path_buffer world path1
 have secondPath:=branchReady.path_buffer world path2
 have noReturn (state : PanSemStateFiniteExact 64 F) (kn ln vn vln leaf : MlS) (value : ValueHOL 64) :
  (evaluateHOLFiniteState state (createBranchLeafSide kn ln vn vln leaf)).1≠some (.returned value) := by
  apply evaluate_noTopReturn
  simp [createBranchLeafSide,branchPayloadStores,branchHeadStore,noTopReturn]
 rw [source_create_branch_two_leaves_1] at tail
 obtain ⟨middle,firstRun,remaining⟩:=seq_returned_of_nonreturning_first (noReturn ready _ _ _ _ _) tail
 obtain ⟨firstLocals,firstSpent,_,live1,size1,heap1,sub1,world1,kinds1,paths1,transport1⟩:=create_branch_leaf_side_normal_world ready middle (insert frontier live) extensions (insert frontier branches) (Function.update size frontier 176) (allocationEnd frontier 176) frontier k1 l1 v1 vl1 readyWorld readyKinds readyPaths firstPath short1 (Or.inl rfl) (ofString "k1") (ofString "l1") (ofString "v1") (ofString "vl1") (ofString "lf1") (by decide) (by decide) branchReady.atPointer readyK1 readyL1 readyV1 readyVL1 readyDomain readyCode (by omega) firstRun
 have firstMetadata:=evaluateHOLFiniteState_metadata ready (createBranchLeafSide (ofString "k1") (ofString "l1") (ofString "v1") (ofString "vl1") (ofString "lf1"))
 rw [firstRun] at firstMetadata
 have middleDomain : ∀address : BitVec 64,address.toNat<33806089496→ middle.memaddrs address := by
  intro address small;rw [firstMetadata.2.1];exact readyDomain address small
 have middleCode : middle.code=originalRuntimeCode:=firstMetadata.1.trans readyCode
 have middlePath:=transport1 k2 l2 secondPath
 have middleBranch : middle.locals.lookup (ofString "br")=some (.val (.word frontier)):=by rw [firstLocals];exact branchReady.atPointer
 have middleK2 : middle.locals.lookup (ofString "k2")=some (.val (.word k2)):=by rw [firstLocals];exact readyK2
 have middleL2 : middle.locals.lookup (ofString "l2")=some (.val (.word l2)):=by rw [firstLocals];exact readyL2
 have middleV2 : middle.locals.lookup (ofString "v2")=some (.val (.word v2)):=by rw [firstLocals];exact readyV2
 have middleVL2 : middle.locals.lookup (ofString "vl2")=some (.val (.word vl2)):=by rw [firstLocals];exact readyVL2
 obtain ⟨lastState,secondRun,returnedRun⟩:=seq_returned_of_nonreturning_first (noReturn middle _ _ _ _ _) remaining
 obtain ⟨secondLocals,_,_,live2,size2,heap2,sub2,world2,kinds2,paths2,transport2⟩:=create_branch_leaf_side_normal_world middle lastState live1 extensions (insert frontier branches) size1 heap1 frontier k2 l2 v2 vl2 world1 kinds1 paths1 middlePath short2 (Or.inl rfl) (ofString "k2") (ofString "l2") (ofString "v2") (ofString "vl2") (ofString "lf2") (by decide) (by decide) middleBranch middleK2 middleL2 middleV2 middleVL2 middleDomain middleCode (by omega) secondRun
 have lastBranch : lastState.locals.lookup (ofString "br")=some (.val (.word frontier)):=by rw [secondLocals];exact middleBranch
 have returnExact : evaluateHOLFiniteState lastState (.return (.var .local (ofString "br")))=
  (some (.returned (.val (.word frontier))),emptyLocalsHOLFinite lastState) := by
  simp [evaluateHOLFiniteState_return,evalHOLExact,lastBranch,shapeOfHOLExact]
 change evaluateHOLFiniteState lastState (.return (.var .local (ofString "br")))=_ at returnedRun
 have returnedEq : returned=.val (.word frontier):=PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj (returnedRun.symm.trans returnExact)).1)
 have outputEq : output=emptyLocalsHOLFinite lastState:=(Prod.mk.inj (returnedRun.symm.trans returnExact)).2
 rw [run,source_create_branch_two_leaves_1,tail] at agreement
 have postMemory : post.memory=lastState.memory:=by rw [agreement.2.2.1,outputEq];rfl
 have postGlobals : post.globals=lastState.globals:=by rw [agreement.2.2.2.1,outputEq];rfl
 have secondMetadata:=evaluateHOLFiniteState_metadata middle (createBranchLeafSide (ofString "k2") (ofString "l2") (ofString "v2") (ofString "vl2") (ofString "lf2"))
 rw [secondRun] at secondMetadata
 have lastDomain : lastState.memaddrs=s.memaddrs:=secondMetadata.2.1.trans (firstMetadata.2.1.trans branchReady.domain)
 have lastEndian : lastState.be=s.be:=secondMetadata.2.2.1.trans (firstMetadata.2.2.1.trans branchReady.endian)
 have postDomain : post.memaddrs=lastState.memaddrs:=metadata.2.1.trans lastDomain.symm
 have postEndian : post.be=lastState.be:=metadata.2.2.1.trans lastEndian.symm
 refine ⟨returnedEq,live2,size2,heap2,fun node member=>sub2 (sub1 member),world2.after_memory_globals postMemory postGlobals,?_,paths2.after_context postMemory postDomain postEndian,?_⟩
 · exact kinds2.after_kind_frame world2.layout.extensionLive world2.layout.branchLive (by intro node registered;rw [postMemory])
 · intro nib len path
   exact (transport2 nib len (transport1 nib len (branchReady.path_buffer world path))).after_context postMemory postDomain postEndian

#print axioms create_branch_two_leaves_returned_world
end InitECandidate.Runtime
