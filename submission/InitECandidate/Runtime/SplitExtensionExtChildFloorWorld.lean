import InitECandidate.Runtime.TrieBranchChildAllocationFloor
import InitECandidate.Runtime.TrieFreshAllocationFloor
import InitECandidate.Runtime.SplitExtensionExtChildWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original nontrivial old-segment arm allocates its real shortened
extension and inserts that pointer at the real loaded nibble. No allocation
room or assumed callee frame is required for this normal-execution endpoint. -/
theorem split_extension_ext_child_normal_floor_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier branch key length matched suffix child : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier)
 (short : length.toNat≤18) (inside : matched.toNat<length.toNat)
 (suffixEq : suffix=length-matched) (long : 1<suffix.toNat)
 (floor : Nat) (lower : TrieAllocationFloor s live branches floor)
 (heapAbove : floor≤frontier.toNat) (keyAbove : floor≤key.toNat)
 (member : branch∈branches) (childValid : child=0∨child∈live)
 (atBranch : s.locals.lookup (ofString "br")=some (.val (.word branch)))
 (atKey : s.locals.lookup (ofString "seg")=some (.val (.word key)))
 (atPrefix : s.locals.lookup (ofString "pl")=some (.val (.word matched)))
 (atSuffix : s.locals.lookup (ofString "sal")=some (.val (.word suffix)))
 (atChild : s.locals.lookup (ofString "child")=some (.val (.word child)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 3≤s.clock)
 (run : evaluateHOLFiniteState s splitExtensionExtChildBody=(none,post)) :
 AllocatedTrieWorld post (insert frontier live) (insert frontier extensions) branches
  (Function.update size frontier 56) (allocationEnd frontier 56) ∧
 TrieNodeKinds post (insert frontier live) (insert frontier extensions) branches ∧
 TrieNodePaths post (insert frontier live) (insert frontier extensions) branches
  (Function.update size frontier 56) (allocationEnd frontier 56) ∧
 TrieAllocationFloor post (insert frontier live) branches floor ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→
  TriePathBuffer post (insert frontier live) (Function.update size frontier 56) nib len (allocationEnd frontier 56)) := by
 have suffixNat : suffix.toNat=length.toNat-matched.toNat := by
  rw [suffixEq,BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))]
 have tailNat : (suffix-1#64).toNat=suffix.toNat-1 :=
  BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1≤suffix.toNat;omega))
 have nonzero : suffix-1#64≠0 := by
  intro zero
  have := congrArg BitVec.toNat zero
  rw [tailNat] at this
  change suffix.toNat-1=0 at this
  omega
 have afterPrefix:=keyPath.suffix (start:=matched) (by omega)
 have afterHead:=afterPrefix.suffix (start:=1#64) (by rw [← suffixEq];change 1≤suffix.toNat;omega)
 have pathTail : TriePathBuffer s live size (key+matched+1) (suffix-1) frontier := by
  change TriePathBuffer s live size (key+matched+1#64) (suffix-1#64) frontier
  rw [suffixEq]
  exact afterHead
 have tailAbove : floor≤(key+matched+1).toNat := by
  have extent : key.toNat+length.toNat<2^64:=by have:=keyPath.extent;have:=frontier.isLt;omega
  simpa [BitVec.ofNat_add,BitVec.add_assoc] using
   trie_path_slice_above_floor key length floor (matched.toNat+1) keyAbove extent (by omega)
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
  [.op .add [.var .local (ofString "seg"),.var .local (ofString "pl"),.const 1],
   .op .sub [.var .local (ofString "sal"),.const 1],.var .local (ofString "child")]=
  some [.val (.word (key+matched+1)),.val (.word (suffix-1)),.val (.word child)] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atKey,atPrefix,atSuffix,atChild,
   wordOpHOL,wordOp,valueIsWord,valueWord,BitVec.add_assoc]
 have reached:=allocated_trie_extension_paths_reaches s (ofString "ex") _
  (branchNibbleStore (ofString "br") (ofString "seg") (ofString "pl") (ofString "ex"))
  frontier (key+matched+1) (suffix-1) child live extensions branches size world kinds paths
  pathTail (by rw [show (suffix-1 : BitVec 64)=suffix-1#64 from rfl,tailNat];omega)
  args childValid nonzero fullDomain code budget
 obtain ⟨ready,⟨extensionReady,readyWorld,readyKinds,readyPaths⟩,_,_,agreement,normal⟩:=
  reaches_normal_continuation s _ _ _ 3 reached (by change (evaluateHOLFiniteState s splitExtensionExtChildBody).1=none;rw [run])
 have lowerReady:=extensionReady.allocation_floor world paths lower heapAbove tailAbove
 have readyBranch : ready.locals.lookup (ofString "br")=some (.val (.word branch)):=
  (extensionReady.locals _ (by decide)).trans atBranch
 have readyKey : ready.locals.lookup (ofString "seg")=some (.val (.word key)):=
  (extensionReady.locals _ (by decide)).trans atKey
 have readyPrefix : ready.locals.lookup (ofString "pl")=some (.val (.word matched)):=
  (extensionReady.locals _ (by decide)).trans atPrefix
 have readyKeyPath:=extensionReady.path_buffer world keyPath
 have readyDomain : ∀address : BitVec 64,address.toNat<33806089496→ ready.memaddrs address:=by
  intro address small;rw [extensionReady.domain];exact fullDomain address small
 cases read : @panMemLoadByteHOL 64 _ ready.memory ready.memaddrs (fun a=>Classical.propDecidable (ready.memaddrs a)) ready.be (key+matched) with
 | none=>
  simp [branchNibbleStore,evaluateHOLFiniteState_store,evalHOLExact,evalListHOLExact,readyBranch,readyKey,readyPrefix,read,wordOpHOL,wordOp,valueIsWord,valueWord,BitVec.add_assoc] at normal
 | some byte=>
  obtain ⟨written,stored,worldOut,kindsOut,pathsOut,_,_,_,_,frame,transport⟩:=
   evaluate_branch_nibble_store_paths_world ready (insert frontier live) (insert frontier extensions) branches
    (Function.update size frontier 56) (allocationEnd frontier 56) readyWorld readyKinds readyPaths
    (ofString "br") (ofString "seg") (ofString "pl") (ofString "ex")
    branch key matched length frontier byte readyBranch readyKey readyPrefix extensionReady.atPointer
    member (Or.inr (Or.inl rfl)) inside readyKeyPath.nibbles read readyDomain
  change Scoped (evaluateHOLFiniteState s splitExtensionExtChildBody)
   (evaluateHOLFiniteState ready (branchNibbleStore (ofString "br") (ofString "seg") (ofString "pl") (ofString "ex"))) at agreement
  rw [run,stored] at agreement
  have memory : post.memory=written.memory:=agreement.2.2.1
  have globals : post.globals=written.globals:=agreement.2.2.2.1
  have metadata:=evaluateHOLFiniteState_metadata s splitExtensionExtChildBody
  rw [run] at metadata
  have storeMetadata:=evaluateHOLFiniteState_metadata ready (branchNibbleStore (ofString "br") (ofString "seg") (ofString "pl") (ofString "ex"))
  rw [stored] at storeMetadata
  have domain : post.memaddrs=written.memaddrs:=metadata.2.1.trans (extensionReady.domain.symm.trans storeMetadata.2.1.symm)
  have endian : post.be=written.be:=metadata.2.2.1.trans (extensionReady.endian.symm.trans storeMetadata.2.2.1.symm)
  have lowerWritten:=lowerReady.after_branch_child readyPaths readyWorld branch member byte.toNat
   (readyKeyPath.nibbles matched.toNat inside byte (by simpa using read)) frame
  refine ⟨worldOut.after_memory_globals memory globals,?_,pathsOut.after_context memory domain endian,lowerWritten.after_memory memory,?_⟩
  · exact kindsOut.after_kind_frame worldOut.layout.extensionLive worldOut.layout.branchLive (by intro node registered;rw [memory])
  · intro nib len path
    exact (transport nib len (extensionReady.path_buffer world path)).after_context memory domain endian

#print axioms split_extension_ext_child_normal_floor_world
end InitECandidate.Runtime
