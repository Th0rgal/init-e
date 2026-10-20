import InitECandidate.Runtime.CreateBranchLeafSideWorld
import InitECandidate.Runtime.TrieBranchChildAllocationFloor
import InitECandidate.Runtime.TrieLeafAllocationFloor
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal execution of the actual first/second leaf side preserves the whole
trie and every existing path buffer. Empty suffixes store a branch payload;
nonempty ones allocate a real leaf and select its slot from the real nibble. -/
theorem create_branch_leaf_side_normal_floor_world {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier branch key length value valueLength : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier) (short : length.toNat≤18)
 (floor : Nat) (lower : TrieAllocationFloor s live branches floor)
 (heapAbove : floor≤frontier.toNat) (keyAbove : floor≤key.toNat)
 (member : branch∈branches)
 (keyName lengthName valueName valueLengthName leafName : MlS)
 (branchSeparate : ofString "br"≠leafName) (keySeparate : keyName≠leafName)
 (atBranch : s.locals.lookup (ofString "br")=some (.val (.word branch)))
 (atKey : s.locals.lookup keyName=some (.val (.word key)))
 (atLength : s.locals.lookup lengthName=some (.val (.word length)))
 (atValue : s.locals.lookup valueName=some (.val (.word value)))
 (atValueLength : s.locals.lookup valueLengthName=some (.val (.word valueLength)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 3≤s.clock)
 (run : evaluateHOLFiniteState s (createBranchLeafSide keyName lengthName valueName valueLengthName leafName)=(none,post)) :
 post.locals=s.locals ∧s.clock≤post.clock+3 ∧post.clock≤s.clock ∧
 ∃larger : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 live⊆larger ∧AllocatedTrieWorld post larger extensions branches newSize finish ∧
 TrieNodeKinds post larger extensions branches ∧TrieNodePaths post larger extensions branches newSize finish ∧
 TrieAllocationFloor post larger branches floor ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) := by
 have fullRun:=run
 have counted:=RunBounded.ofProg (create_branch_leaf_side_bounded keyName lengthName valueName valueLengthName leafName) code budget
 unfold RunBounded at counted
 rw [run] at counted
 have locals : post.locals=s.locals := by
  apply HolFiniteMapExact.ext
  funext name
  have supported : avoidsLocal name (createBranchLeafSide keyName lengthName valueName valueLengthName leafName)=true := by
   simp [createBranchLeafSide,branchPayloadStores,branchHeadStore,avoidsLocal]
  have kept:=evaluate_avoidsLocal_flowing name _ supported s
  rw [run] at kept
  exact kept (Or.inl rfl)
 have metadata:=evaluateHOLFiniteState_metadata s (createBranchLeafSide keyName lengthName valueName valueLengthName leafName)
 rw [run] at metadata
 refine ⟨locals,counted.1,counted.2.1,?_⟩
 have cmp : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.cmp .equal (.var .local lengthName) (.const 0))=some (.val (.word (if length=0#64 then 1#64 else 0#64))) := by
  simp [evalHOLExact,atLength,Compiler.Encoders.Asm.wordCmpHOL]
 unfold createBranchLeafSide at run
 rw [evaluateHOLFiniteState_ite,cmp] at run
 by_cases empty : length=0#64
 · simp only [if_pos empty,show (1#64)≠0 from by decide,if_false] at run
   obtain ⟨written,stored,worldOut,kindsOut,pathsOut,_,_,_,_,_,frame,transport⟩:=evaluate_branch_payload_stores_world s live extensions branches size frontier world kinds paths (ofString "br") valueName valueLengthName branch value valueLength member atBranch atValue atValueLength fullDomain
   have same : post=written:=(Prod.mk.inj (run.symm.trans stored)).2
   subst post
   have lowerOut : TrieAllocationFloor written live branches floor := by
    apply lower.after_record_fields paths world branch (world.layout.branchLive member) [160,168]
    · intro field included
      simp only [List.mem_cons,List.not_mem_nil,or_false] at included
      have:=world.layout.branchSize branch member
      rcases included with rfl|rfl <;>omega
    · exact Or.inl member
    · intro watched separate
      exact frame watched (separate 160 (by simp)) (separate 168 (by simp))
   exact ⟨live,size,frontier,fun _ h=>h,worldOut,kindsOut,pathsOut,lowerOut,transport⟩
 · simp only [if_neg empty] at run
   change evaluateHOLFiniteState s (.decCall leafName .one (ofString "node_new_leaf")
    [.op .add [.var .local keyName,.const 1],.op .sub [.var .local lengthName,.const 1],.var .local valueName,.var .local valueLengthName]
    (branchHeadStore (ofString "br") keyName leafName))=(none,post) at run
   have positive : 0<length.toNat:=by have : length.toNat≠0:=fun h=>empty (BitVec.eq_of_toNat_eq h);omega
   have suffix:=keyPath.suffix (start:=1#64) (by change 1≤length.toNat;omega)
   have lengthSub : (length-1#64).toNat=length.toNat-1:=BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1≤length.toNat;omega))
   have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
    [.op .add [.var .local keyName,.const 1],.op .sub [.var .local lengthName,.const 1],.var .local valueName,.var .local valueLengthName]=
    some [.val (.word (key+1)),.val (.word (length-1)),.val (.word value),.val (.word valueLength)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atKey,atLength,atValue,atValueLength,wordOpHOL,wordOp,valueIsWord,valueWord]
   have reached:=allocated_trie_leaf_paths_reaches s leafName _ (branchHeadStore (ofString "br") keyName leafName)
    frontier (key+1) (length-1) value valueLength live extensions branches size world kinds paths suffix
    (by rw [show (length-1 : BitVec 64)=length-1#64 from rfl,lengthSub];omega) args fullDomain code budget
   obtain ⟨ready,⟨leafReady,readyWorld,readyKinds,readyPaths⟩,_,_,agreement,normal⟩:=reaches_normal_continuation s _ _ _ 3 reached (by rw [run])
   have tailAbove : floor≤(key+1).toNat := by
    have extent : key.toNat+length.toNat<2^64:=by have:=keyPath.extent;have:=frontier.isLt;omega
    simpa using trie_path_slice_above_floor key length floor 1 keyAbove extent (by omega)
   have lowerReady:=leafReady.allocation_floor world paths lower heapAbove tailAbove
   have readyBranch : ready.locals.lookup (ofString "br")=some (.val (.word branch)) := (leafReady.locals _ branchSeparate).trans atBranch
   have readyKey : ready.locals.lookup keyName=some (.val (.word key)) := (leafReady.locals _ keySeparate).trans atKey
   have readyKeyPath:=leafReady.path_buffer world keyPath
   have readyDomain : ∀address : BitVec 64,address.toNat<33806089496→ ready.memaddrs address:=by
    intro address small;rw [leafReady.domain];exact fullDomain address small
   cases read : @panMemLoadByteHOL 64 _ ready.memory ready.memaddrs (fun a=>Classical.propDecidable (ready.memaddrs a)) ready.be key with
   | none=>
    simp [branchHeadStore,evaluateHOLFiniteState_store,evalHOLExact,evalListHOLExact,readyBranch,readyKey,read] at normal
   | some byte=>
    obtain ⟨written,stored,worldOut,kindsOut,pathsOut,_,_,_,_,frame,transport⟩:=evaluate_branch_head_store_world ready (insert frontier live) extensions branches (Function.update size frontier 64) (allocationEnd frontier 64) readyWorld readyKinds readyPaths (ofString "br") keyName leafName branch key length frontier byte readyBranch readyKey leafReady.atPointer member (Or.inr (Or.inl rfl)) positive readyKeyPath.nibbles read readyDomain
    rw [run,stored] at agreement
    have memory : post.memory=written.memory:=agreement.2.2.1
    have globals : post.globals=written.globals:=agreement.2.2.2.1
    have storeMetadata:=evaluateHOLFiniteState_metadata ready (branchHeadStore (ofString "br") keyName leafName)
    rw [stored] at storeMetadata
    have domain : post.memaddrs=written.memaddrs:=metadata.2.1.trans (leafReady.domain.symm.trans storeMetadata.2.1.symm)
    have endian : post.be=written.be:=metadata.2.2.1.trans (leafReady.endian.symm.trans storeMetadata.2.2.1.symm)
    have lowerWritten:=lowerReady.after_branch_child readyPaths readyWorld branch member byte.toNat
     (readyKeyPath.nibbles 0 (by omega) byte (by simpa using read)) frame
    refine ⟨insert frontier live,Function.update size frontier 64,allocationEnd frontier 64,fun _ h=>Or.inr h,
     worldOut.after_memory_globals memory globals,?_,pathsOut.after_context memory domain endian,lowerWritten.after_memory memory,?_⟩
    · exact kindsOut.after_kind_frame worldOut.layout.extensionLive worldOut.layout.branchLive (by intro node registered;rw [memory])
    · intro nib len path
      exact (transport nib len (leafReady.path_buffer world path)).after_context memory domain endian

#print axioms create_branch_leaf_side_normal_floor_world
end InitECandidate.Runtime
