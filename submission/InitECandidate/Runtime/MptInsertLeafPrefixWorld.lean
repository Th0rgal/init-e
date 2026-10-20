import InitECandidate.Runtime.MptInsertLeafBranchWorld
import InitECandidate.Runtime.CommonPrefixReturnedFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original divergent-leaf prefix call supplies its real length bounds,
read-only state and remaining clock to the actual branch/extension tail. -/
theorem mpt_insert_leaf_prefix_returned_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier node oldKey oldLength key length value valueLength : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier) (short : length.toNat≤18)
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
 (code : s.code=originalRuntimeCode) (budget : 71≤s.clock) (returned : ValueHOL 64)
 (run : evaluateHOLFiniteState s (mptInsertLeafAt 3)=(some (.returned returned),post)) :
 ∃root : BitVec 64,∃larger newExtensions : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 returned=.val (.word root) ∧root∈larger ∧live⊆larger ∧extensions⊆newExtensions ∧
 AllocatedTrieWorld post larger newExtensions (insert frontier branches) newSize finish ∧
 TrieNodeKinds post larger newExtensions (insert frontier branches) ∧
 TrieNodePaths post larger newExtensions (insert frontier branches) newSize finish ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) := by
 have minBound : (wordMin oldLength length).toNat≤18 := by
  unfold wordMin
  split
  · rename_i small
    omega
  · exact short
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
  [.var .local (ofString "ek"),.var .local (ofString "el"),.var .local (ofString "rk"),.var .local (ofString "rl")]=
   some [.val (.word oldKey),.val (.word oldLength),.val (.word key),.val (.word length)] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atOldKey,atOldLength,atKey,atLength]
 rw [source_mpt_insert_leaf_3] at run
 obtain ⟨matched,bodyPost,output,oldBound,newBound,spent,clock,memory,globals,domains,endian,installed,tailRun,scope⟩:=
  common_prefix_declaration_returned_frame s post (ofString "pl") _ (mptInsertLeafAt 4) oldKey oldLength key length
   returned args code (by omega) run
 let ready:=setVarHOLFinite (ofString "pl") (.val (.word matched)) {bodyPost with locals:=s.locals}
 have readyWorld : AllocatedTrieWorld ready live extensions branches size frontier:=world.after_memory_globals memory globals
 have readyKinds : TrieNodeKinds ready live extensions branches:=
  kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive (by intro node member;exact congrFun memory node)
 have readyLocal (name : MlS) (separate : name≠ofString "pl") : ready.locals.lookup name=s.locals.lookup name := by
  simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,separate,Ne.symm separate]
 obtain ⟨root,larger,newExtensions,newSize,finish,returnedEq,rootLive,sub,extSub,worldOut,kindsOut,pathsOut,transport⟩:=
  mpt_insert_leaf_branch_returned_world ready output live extensions branches size frontier node oldKey oldLength key length matched
   value valueLength readyWorld readyKinds (paths.after_context memory domains endian) (keyPath.after_context memory domains endian)
   short nodeLive nonExt nonBranch (by rw [show ready.memory=s.memory from memory];exact memoryKey)
   (by rw [show ready.memory=s.memory from memory];exact memoryLength) oldBound newBound
   ((readyLocal _ (by decide)).trans atNode) ((readyLocal _ (by decide)).trans atOldKey)
   ((readyLocal _ (by decide)).trans atOldLength) ((readyLocal _ (by decide)).trans atKey)
   ((readyLocal _ (by decide)).trans atLength)
   (by simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   ((readyLocal _ (by decide)).trans atValue) ((readyLocal _ (by decide)).trans atValueLength)
   (by intro address small;change bodyPost.memaddrs address;rw [domains];exact fullDomain address small)
   (installed.trans code) (by change 51≤bodyPost.clock;omega) returned tailRun
 have postMemory : post.memory=output.memory:=by rw [scope]
 have postGlobals : post.globals=output.globals:=by rw [scope]
 have postDomains : post.memaddrs=output.memaddrs:=by rw [scope]
 have postEndian : post.be=output.be:=by rw [scope]
 refine ⟨root,larger,newExtensions,newSize,finish,returnedEq,rootLive,sub,extSub,
  worldOut.after_memory_globals postMemory postGlobals,?_,pathsOut.after_context postMemory postDomains postEndian,?_⟩
 · exact kindsOut.after_kind_frame worldOut.layout.extensionLive worldOut.layout.branchLive (by intro node member;rw [postMemory])
 · intro nib len path
   exact (transport nib len (path.after_context memory domains endian)).after_context postMemory postDomains postEndian

#print axioms mpt_insert_leaf_prefix_returned_world
end InitECandidate.Runtime
