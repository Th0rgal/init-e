import InitECandidate.Runtime.MptInsertExtensionSplitWorld
import InitECandidate.Runtime.SplitExtensionDeclarationFloorWorld
import InitECandidate.Runtime.MptInsertExtensionSplitTailFloorWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete actual extension split arm includes its real six-argument
splitter declaration and optional extension constructor. Both fresh branches
and extensions are derived from source executions, with all paths preserved. -/
theorem mpt_insert_extension_split_normal_floor_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier node segment segmentLength key length level matched value valueLength oldResult : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier) (short : length.toNat≤18)
 (floor : Nat) (lower : TrieAllocationFloor s live branches floor)
 (heapAbove : floor≤frontier.toNat) (keyAbove : floor≤key.toNat)
 (extension : node∈extensions)
 (memoryKey : s.memory (node+32#64)=.word segment)
 (memoryLength : s.memory (node+40#64)=.word segmentLength)
 (inside : matched.toNat<segmentLength.toNat) (matchedBound : matched.toNat≤(length-level).toNat)
 (levelBound : level.toNat≤length.toNat)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atSegment : s.locals.lookup (ofString "seg")=some (.val (.word segment)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atLevel : s.locals.lookup (ofString "level")=some (.val (.word level)))
 (atMatched : s.locals.lookup (ofString "pl")=some (.val (.word matched)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (atResult : s.locals.lookup (ofString "r")=some (.val (.word oldResult)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 51≤s.clock)
 (run : evaluateHOLFiniteState s mptInsertExtensionSplit=(none,post)) :
 ∃root : BitVec 64,∃larger newExtensions : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 post.locals.lookup (ofString "r")=some (.val (.word root)) ∧root∈larger ∧live⊆larger ∧extensions⊆newExtensions ∧
 AllocatedTrieWorld post larger newExtensions (insert frontier branches) newSize finish ∧
 TrieNodeKinds post larger newExtensions (insert frontier branches) ∧
 TrieNodePaths post larger newExtensions (insert frontier branches) newSize finish ∧
 TrieAllocationFloor post larger (insert frontier branches) floor ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) ∧
 (∀other : MlS,other≠ofString "r"→ other≠ofString "br"→post.locals.lookup other=s.locals.lookup other) := by
 have nodeLive:=world.layout.extensionLive extension
 have nonBranch : node∉branches:=fun member=>Set.disjoint_left.mp world.layout.differentKinds extension member
 obtain ⟨storedKey,storedLength,keyAt,lengthAt,oldShort,oldPath⟩:=paths.paths node nodeLive nonBranch
 have keyEq : storedKey=segment:=HolWordLab.word.inj (keyAt.symm.trans memoryKey)
 have lengthEq : storedLength=segmentLength:=HolWordLab.word.inj (lengthAt.symm.trans memoryLength)
 rw [keyEq,lengthEq] at oldPath
 rw [lengthEq] at oldShort
 have remainder : (length-level).toNat≤18 := by
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr levelBound)];omega
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
  [.var .local (ofString "node"),.op .add [.var .local (ofString "key"),.var .local (ofString "level")],
   .op .sub [.var .local (ofString "klen"),.var .local (ofString "level")],
   .var .local (ofString "vptr"),.var .local (ofString "vlen"),.var .local (ofString "pl")]=
  some [.val (.word node),.val (.word (key+level)),.val (.word (length-level)),
   .val (.word value),.val (.word valueLength),.val (.word matched)] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atNode,atKey,atLength,atLevel,atValue,atValueLength,
   atMatched,wordOpHOL,wordOp,valueIsWord,valueWord]
 rw [source_mptInsert_extension_split] at run
 obtain ⟨bodyPost,output,middleLive,middleExtensions,middleSize,middleFinish,sub,extSub,
  middleWorld,middleKinds,middlePaths,middleLower,transport,domains,endian,installed,tailRun,scope⟩:=
  split_extension_declaration_floor_world s post (ofString "br") _ mptInsertExtensionSplitTail live extensions branches size
   frontier node segmentLength (key+level) (length-level) matched value valueLength world kinds paths
   (keyPath.suffix levelBound) remainder floor lower heapAbove
   (by have extent : key.toNat+length.toNat<2^64:=by have:=keyPath.extent;have:=frontier.isLt;omega
       simpa using trie_path_slice_above_floor key length floor level.toNat keyAbove extent levelBound) extension memoryLength inside matchedBound args fullDomain code budget run
 let ready:=setVarHOLFinite (ofString "br") (.val (.word frontier)) {bodyPost with locals:=s.locals}
 have readyWorld : AllocatedTrieWorld ready middleLive middleExtensions (insert frontier branches) middleSize middleFinish:=
  middleWorld.after_memory_globals rfl rfl
 have readyKinds : TrieNodeKinds ready middleLive middleExtensions (insert frontier branches):=
  middleKinds.after_kind_frame middleWorld.layout.extensionLive middleWorld.layout.branchLive (by intro current member;rfl)
 have readyLocal (name : MlS) (different : name≠ofString "br") : ready.locals.lookup name=s.locals.lookup name := by
  simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different]
 obtain ⟨root,larger,newExtensions,newSize,finish,assigned,rootLive,liveSub,extensionsSub,
  worldOut,kindsOut,pathsOut,lowerOut,tailTransport,locals⟩:=mpt_insert_extension_split_tail_floor_world ready output
   middleLive middleExtensions (insert frontier branches) middleSize middleFinish segment segmentLength matched frontier oldResult
   readyWorld readyKinds (middlePaths.after_context rfl rfl rfl)
   ((transport segment segmentLength oldPath).after_context rfl rfl rfl) oldShort (by omega) floor (middleLower.after_memory rfl)
   (by have bound:=middleLower.records frontier (sub (Or.inl rfl));have allocated:=middleWorld.allocated frontier (sub (Or.inl rfl));omega)
   (lower.keys node nodeLive nonBranch segment segmentLength memoryKey memoryLength)
   (sub (Or.inl rfl)) ((readyLocal _ (by decide)).trans atSegment) ((readyLocal _ (by decide)).trans atMatched)
   (by simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) ((readyLocal _ (by decide)).trans atResult)
   (by intro address bound;change bodyPost.memaddrs address;rw [domains];exact fullDomain address bound)
   (installed.trans code) tailRun
 have postMemory : post.memory=output.memory:=by rw [scope]
 have postGlobals : post.globals=output.globals:=by rw [scope]
 have postDomains : post.memaddrs=output.memaddrs:=by rw [scope]
 have postEndian : post.be=output.be:=by rw [scope]
 refine ⟨root,larger,newExtensions,newSize,finish,?_,rootLive,?_,?_,
  worldOut.after_memory_globals postMemory postGlobals,?_,pathsOut.after_context postMemory postDomains postEndian,lowerOut.after_memory postMemory,?_,?_⟩
 · rw [scope,saved_local_lookup_other output.locals (ofString "br") (ofString "r") _ (by decide)]
   exact assigned
 · intro current member;exact liveSub (sub (Or.inr member))
 · intro current member;exact extensionsSub (extSub member)
 · exact kindsOut.after_kind_frame worldOut.layout.extensionLive worldOut.layout.branchLive
    (by intro current member;rw [postMemory])
 · intro nib len path
   exact (tailTransport nib len ((transport nib len path).after_context rfl rfl rfl)).after_context postMemory postDomains postEndian
 · intro other notR notBr
   rw [scope,saved_local_lookup_other output.locals (ofString "br") other _ notBr]
   exact (locals other notR).trans (readyLocal other notBr)

#print axioms mpt_insert_extension_split_normal_floor_world
end InitECandidate.Runtime
