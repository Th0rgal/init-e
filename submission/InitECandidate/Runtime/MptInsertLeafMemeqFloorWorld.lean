import InitECandidate.Runtime.MemeqReturnedFrame
import InitECandidate.Runtime.MptInsertLeafEqualFloorWorld
import InitECandidate.Runtime.TrieNodePathsContext
import InitECandidate.Runtime.MptInsertLeafEqualTestNormalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual equal-length memeq declaration, when it returns through its
source continuation, returns the original live leaf after its two payload
stores, preserving every separated path buffer and the heap frontier. -/
theorem mpt_insert_leaf_memeq_returned_floor_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier node oldKey key length value valueLength : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (floor : Nat) (lower : TrieAllocationFloor s live branches floor)
 (nodeLive : node∈live) (tag : s.memory node=.word (1#64))
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atOldKey : s.locals.lookup (ofString "ek")=some (.val (.word oldKey)))
 (atOldLength : s.locals.lookup (ofString "el")=some (.val (.word length)))
 (atKey : s.locals.lookup (ofString "rk")=some (.val (.word key)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (small : length.toNat≤64) (budget : 4*length.toNat+1≤s.clock)
 (returned : ValueHOL 64)
 (run : evaluateHOLFiniteState s
  (.decCall (ofString "eq") .one (ofString "memeq")
   [.var .local (ofString "ek"),.var .local (ofString "rk"),.var .local (ofString "el")]
   mptInsertLeafEqualReturn)=(some (.returned returned),post)) :
 returned=.val (.word node) ∧
 AllocatedTrieWorld post live extensions branches size frontier ∧TrieNodeKinds post live extensions branches ∧
 TrieNodePaths post live extensions branches size frontier ∧post.globals=s.globals ∧
 TrieAllocationFloor post live branches floor ∧
 (∀key len,TriePathBuffer s live size key len frontier→TriePathBuffer post live size key len frontier) := by
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
  [.var .local (ofString "ek"),.var .local (ofString "rk"),.var .local (ofString "el")]=
   some [.val (.word oldKey),.val (.word key),.val (.word length)] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atOldKey,atKey,atOldLength]
 obtain ⟨found,bodyPost,output,spent,clock,memory,globals,domains,endian,installed,tailRun,scope⟩:=
  memeq_declaration_returned_frame s post (ofString "eq") _ mptInsertLeafEqualReturn
   oldKey key length returned args code small budget run
 let ready:=setVarHOLFinite (ofString "eq") (.val (.word found)) {bodyPost with locals:=s.locals}
 have readyLocal (name : MlS) (different : name≠ofString "eq") : ready.locals.lookup name=s.locals.lookup name := by
  simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different]
 have readyWorld : AllocatedTrieWorld ready live extensions branches size frontier:=world.after_memory_globals memory globals
 have readyKinds : TrieNodeKinds ready live extensions branches:=
  kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive (by intro node member;exact congrFun memory node)

 obtain ⟨returnedEq,worldOut,kindsOut,pathsOut,outputGlobals,lowerOut,transport⟩:=
  mpt_insert_leaf_equal_returned_floor_world ready output live extensions branches size frontier
   node value valueLength readyWorld readyKinds (paths.after_context memory domains endian) floor (lower.after_memory memory) nodeLive
   ((congrFun memory node).trans tag) ((readyLocal _ (by decide)).trans atNode)
   ((readyLocal _ (by decide)).trans atValue) ((readyLocal _ (by decide)).trans atValueLength)
   (by intro address bound;change bodyPost.memaddrs address;rw [domains];exact fullDomain address bound)
   returned tailRun
 have postMemory : post.memory=output.memory:=by rw [scope]
 have postGlobals : post.globals=output.globals:=by rw [scope]
 have postDomains : post.memaddrs=output.memaddrs:=by rw [scope]
 have postEndian : post.be=output.be:=by rw [scope]
 refine ⟨returnedEq,worldOut.after_memory_globals postMemory postGlobals,?_,
  pathsOut.after_context postMemory postDomains postEndian,?_,lowerOut.after_memory postMemory,?_⟩
 · exact kindsOut.after_kind_frame worldOut.layout.extensionLive worldOut.layout.branchLive
    (by intro current member;rw [postMemory])
 · exact postGlobals.trans (outputGlobals.trans globals)
 · intro key len path
   exact (transport key len (path.after_context memory domains endian)).after_context postMemory postDomains postEndian

#print axioms mpt_insert_leaf_memeq_returned_floor_world
/-- The complete original length-test arm can return only through the
actual memeq continuation and payload stores; unequal lengths take skip. -/
theorem mpt_insert_leaf_equal_test_returned_floor_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier node oldKey key length value valueLength : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (floor : Nat) (lower : TrieAllocationFloor s live branches floor)
 (nodeLive : node∈live) (tag : s.memory node=.word (1#64))
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atOldKey : s.locals.lookup (ofString "ek")=some (.val (.word oldKey)))
 (atOldLength : s.locals.lookup (ofString "el")=some (.val (.word length)))
 (atKey : s.locals.lookup (ofString "rk")=some (.val (.word key)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (small : length.toNat≤64) (budget : 4*length.toNat+1≤s.clock)
 (returned : ValueHOL 64)
 (run : evaluateHOLFiniteState s
  mptInsertLeafEqualTest=(some (.returned returned),post)) :
 returned=.val (.word node) ∧
 AllocatedTrieWorld post live extensions branches size frontier ∧TrieNodeKinds post live extensions branches ∧
 TrieNodePaths post live extensions branches size frontier ∧post.globals=s.globals ∧
 TrieAllocationFloor post live branches floor ∧
 (∀key len,TriePathBuffer s live size key len frontier→TriePathBuffer post live size key len frontier) := by
 rw [source_mpt_insert_leaf_equal_test,evaluateHOLFiniteState_ite] at run
 split at run
 · split at run
   · rw [evaluateHOLFiniteState_skip] at run
     cases run
   · exact mpt_insert_leaf_memeq_returned_floor_world s post live extensions branches size frontier
      node oldKey key length value valueLength world kinds paths floor lower nodeLive tag atNode atOldKey atOldLength
      atKey atValue atValueLength fullDomain code small budget returned run
 · simp at run

#print axioms mpt_insert_leaf_equal_test_returned_floor_world
end InitECandidate.Runtime
