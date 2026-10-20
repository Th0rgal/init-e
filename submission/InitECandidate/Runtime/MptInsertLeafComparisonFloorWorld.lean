import InitECandidate.Runtime.MptInsertLeafPrefixFloorWorld
import InitECandidate.Runtime.MptInsertLeafMemeqFloorWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual leaf comparison sequence: equal-key payload return and
fallthrough into original prefix/branch/extension construction both preserve
the allocated trie world and every separated path buffer. Stored old length
is derived from the actual node-path invariant, earning all callee clocks. -/
theorem mpt_insert_leaf_comparison_returned_floor_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier node oldKey oldLength key length value valueLength : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier) (short : length.toNat≤18)
 (floor : Nat) (lower : TrieAllocationFloor s live branches floor)
 (heapAbove : floor≤frontier.toNat) (keyAbove : floor≤key.toNat)
 (nodeLive : node∈live) (nonExt : node∉extensions) (nonBranch : node∉branches)
 (memoryKey : s.memory (node+32#64)=.word oldKey)
 (memoryLength : s.memory (node+40#64)=.word oldLength)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atOldKey : s.locals.lookup (ofString "ek")=some (.val (.word oldKey)))
 (atOldLength : s.locals.lookup (ofString "el")=some (.val (.word oldLength)))
 (atKey : s.locals.lookup (ofString "rk")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "rl")=some (.val (.word length)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 144≤s.clock) (returned : ValueHOL 64)
 (run : evaluateHOLFiniteState s (mptInsertLeafAt 2)=(some (.returned returned),post)) :
 ∃root : BitVec 64,∃larger newExtensions newBranches : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 returned=.val (.word root) ∧root∈larger ∧live⊆larger ∧extensions⊆newExtensions ∧branches⊆newBranches ∧
 AllocatedTrieWorld post larger newExtensions newBranches newSize finish ∧
 TrieNodeKinds post larger newExtensions newBranches ∧
 TrieNodePaths post larger newExtensions newBranches newSize finish ∧
 TrieAllocationFloor post larger newBranches floor ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) := by
 obtain ⟨storedKey,storedLength,keyAt,lengthAt,storedShort,storedPath⟩:=paths.paths node nodeLive nonBranch
 have sameLength : storedLength=oldLength:=HolWordLab.word.inj (lengthAt.symm.trans memoryLength)
 have oldShort : oldLength.toNat≤18:=by rw [←sameLength];exact storedShort
 have tag : s.memory node=.word (1#64):=kinds.leaf node nodeLive nonExt nonBranch
 have small : oldLength.toNat≤64:=by omega
 have ticks : 4*oldLength.toNat+1≤s.clock:=by omega
 have sequence : mptInsertLeafAt 2=.seq mptInsertLeafEqualTest (mptInsertLeafAt 3):=rfl
 rw [sequence,evaluateHOLFiniteState_seq_line780] at run
 cases firstRun : evaluateHOLFiniteState s mptInsertLeafEqualTest with
 | mk result middle =>
  rw [firstRun] at run
  cases result with
  | none =>
   dsimp only at run
   obtain ⟨memory,globals,domains,endian,installed,spent,clock,locals⟩:=
    mpt_insert_leaf_equal_test_normal_frame s middle live extensions branches size frontier node oldKey key oldLength
     value valueLength world kinds paths nodeLive tag atNode atOldKey atOldLength atKey atValue atValueLength
     fullDomain code small ticks firstRun
   have middleWorld : AllocatedTrieWorld middle live extensions branches size frontier:=world.after_memory_globals memory globals
   have middleKinds : TrieNodeKinds middle live extensions branches:=
    kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive (by intro n member;exact congrFun memory n)
   obtain ⟨root,larger,newExtensions,newSize,finish,valueEq,rootLive,sub,extSub,worldOut,kindsOut,pathsOut,lowerOut,transport⟩:=
    mpt_insert_leaf_prefix_returned_floor_world middle post live extensions branches size frontier node oldKey oldLength key length
     value valueLength middleWorld middleKinds (paths.after_context memory domains endian)
     (keyPath.after_context memory domains endian) short floor (lower.after_memory memory) heapAbove keyAbove nodeLive nonExt nonBranch
     ((congrFun memory (node+32#64)).trans memoryKey) ((congrFun memory (node+40#64)).trans memoryLength)
     ((locals _ (by decide)).trans atNode) ((locals _ (by decide)).trans atOldKey)
     ((locals _ (by decide)).trans atOldLength) ((locals _ (by decide)).trans atKey)
     ((locals _ (by decide)).trans atLength) ((locals _ (by decide)).trans atValue)
     ((locals _ (by decide)).trans atValueLength)
     (by intro address bound;rw [domains];exact fullDomain address bound)
     (installed.trans code) (by omega) returned run
   refine ⟨root,larger,newExtensions,insert frontier branches,newSize,finish,valueEq,rootLive,sub,extSub,
    ?_,worldOut,kindsOut,pathsOut,lowerOut,?_⟩
   · intro n member;exact Set.mem_insert_of_mem frontier member
   · intro nib len path
     exact transport nib len (path.after_context memory domains endian)
  | some result =>
   change (some result,middle)=(some (.returned returned),post) at run
   have resultEq : result=.returned returned:=Option.some.inj (Prod.mk.inj run).1
   subst result
   have same : middle=post:=(Prod.mk.inj run).2
   subst middle
   obtain ⟨valueEq,worldOut,kindsOut,pathsOut,globals,lowerOut,transport⟩:=
    mpt_insert_leaf_equal_test_returned_floor_world s post live extensions branches size frontier node oldKey key oldLength
     value valueLength world kinds paths floor lower nodeLive tag atNode atOldKey atOldLength atKey atValue atValueLength
     fullDomain code small ticks returned firstRun
   exact ⟨node,live,extensions,branches,size,frontier,valueEq,nodeLive,(fun _ h=>h),(fun _ h=>h),
    (fun _ h=>h),worldOut,kindsOut,pathsOut,lowerOut,transport⟩

#print axioms mpt_insert_leaf_comparison_returned_floor_world
end InitECandidate.Runtime
