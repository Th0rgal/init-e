import InitECandidate.Runtime.TrieBranchChildAllocationFloor
import InitECandidate.Runtime.TrieFreshAllocationFloor
import InitECandidate.Runtime.SplitExtensionLeafChildWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original incoming-leaf constructor and store preserve the complete
allocated world. Its real shortened key slice supplies the new leaf path. -/
theorem split_extension_leaf_child_normal_floor_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier branch key length matched suffix slot value valueLength : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier)
 (short : length.toNat≤18) (inside : matched.toNat<length.toNat)
 (suffixEq : suffix=length-matched) (small : slot.toNat<16)
 (floor : Nat) (lower : TrieAllocationFloor s live branches floor)
 (heapAbove : floor≤frontier.toNat) (keyAbove : floor≤key.toNat)
 (member : branch∈branches)
 (atBranch : s.locals.lookup (ofString "br")=some (.val (.word branch)))
 (atKey : s.locals.lookup (ofString "rk")=some (.val (.word key)))
 (atMatched : s.locals.lookup (ofString "pl")=some (.val (.word matched)))
 (atSuffix : s.locals.lookup (ofString "kal")=some (.val (.word suffix)))
 (atSlot : s.locals.lookup (ofString "idx")=some (.val (.word slot)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 3≤s.clock)
 (run : evaluateHOLFiniteState s splitExtensionLeafChildBody=(none,post)) :
 AllocatedTrieWorld post (insert frontier live) extensions branches
  (Function.update size frontier 64) (allocationEnd frontier 64) ∧
 TrieNodeKinds post (insert frontier live) extensions branches ∧
 TrieNodePaths post (insert frontier live) extensions branches
  (Function.update size frontier 64) (allocationEnd frontier 64) ∧
 TrieAllocationFloor post (insert frontier live) branches floor ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→
  TriePathBuffer post (insert frontier live) (Function.update size frontier 64) nib len (allocationEnd frontier 64)) := by
 have suffixNat : suffix.toNat=length.toNat-matched.toNat := by
  rw [suffixEq,BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))]
 have tailNat : (suffix-1#64).toNat=suffix.toNat-1 :=
  BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1≤suffix.toNat;omega))
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
  [.op .add [.var .local (ofString "rk"),.var .local (ofString "pl"),.const 1],
   .op .sub [.var .local (ofString "kal"),.const 1],
   .var .local (ofString "vptr"),.var .local (ofString "vlen")]=
  some [.val (.word (key+matched+1)),.val (.word (suffix-1)),.val (.word value),.val (.word valueLength)] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atKey,atMatched,atSuffix,atValue,atValueLength,
   wordOpHOL,wordOp,valueIsWord,valueWord,BitVec.add_assoc]
 have reached:=allocated_trie_leaf_paths_reaches s (ofString "lf") _
  (branchSlotStore (ofString "br") (ofString "idx") (ofString "lf"))
  frontier (key+matched+1) (suffix-1) value valueLength live extensions branches size world kinds paths
  pathTail (by rw [show (suffix-1 : BitVec 64)=suffix-1#64 from rfl,tailNat];omega)
  args fullDomain code budget
 obtain ⟨ready,⟨leafReady,readyWorld,readyKinds,readyPaths⟩,_,_,agreement,normal⟩:=
  reaches_normal_continuation s _ _ _ 3 reached (by change (evaluateHOLFiniteState s splitExtensionLeafChildBody).1=none;rw [run])
 have lowerReady:=leafReady.allocation_floor world paths lower heapAbove tailAbove
 have readyBranch : ready.locals.lookup (ofString "br")=some (.val (.word branch)):=
  (leafReady.locals _ (by decide)).trans atBranch
 have readySlot : ready.locals.lookup (ofString "idx")=some (.val (.word slot)):=
  (leafReady.locals _ (by decide)).trans atSlot
 have readyDomain : ∀address : BitVec 64,address.toNat<33806089496→ ready.memaddrs address:=by
  intro address small;rw [leafReady.domain];exact fullDomain address small
 obtain ⟨written,stored,worldOut,kindsOut,pathsOut,_,_,_,_,frame,transport⟩:=
  evaluate_branch_slot_store_world ready (insert frontier live) extensions branches
   (Function.update size frontier 64) (allocationEnd frontier 64) readyWorld readyKinds readyPaths
   (ofString "br") (ofString "idx") (ofString "lf") branch slot frontier
   readyBranch readySlot leafReady.atPointer member (Or.inr (Or.inl rfl)) small readyDomain
 change Scoped (evaluateHOLFiniteState s splitExtensionLeafChildBody)
  (evaluateHOLFiniteState ready (branchSlotStore (ofString "br") (ofString "idx") (ofString "lf"))) at agreement
 rw [run,stored] at agreement
 have memory : post.memory=written.memory:=agreement.2.2.1
 have globals : post.globals=written.globals:=agreement.2.2.2.1
 have metadata:=evaluateHOLFiniteState_metadata s splitExtensionLeafChildBody
 rw [run] at metadata
 have storeMetadata:=evaluateHOLFiniteState_metadata ready (branchSlotStore (ofString "br") (ofString "idx") (ofString "lf"))
 rw [stored] at storeMetadata
 have domain : post.memaddrs=written.memaddrs:=metadata.2.1.trans (leafReady.domain.symm.trans storeMetadata.2.1.symm)
 have endian : post.be=written.be:=metadata.2.2.1.trans (leafReady.endian.symm.trans storeMetadata.2.2.1.symm)
 have lowerWritten:=lowerReady.after_branch_child readyPaths readyWorld branch member slot.toNat small frame
 refine ⟨worldOut.after_memory_globals memory globals,?_,pathsOut.after_context memory domain endian,lowerWritten.after_memory memory,?_⟩
 · exact kindsOut.after_kind_frame worldOut.layout.extensionLive worldOut.layout.branchLive (by intro node registered;rw [memory])
 · intro nib len path
   exact (transport nib len (leafReady.path_buffer world path)).after_context memory domain endian

#print axioms split_extension_leaf_child_normal_floor_world
end InitECandidate.Runtime
